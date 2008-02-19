/*
Copyright (C) 2007 Leo Freitas
This file is part of the czt project.
The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.
The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.typecheck.circus;

import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.BasicProcessSignature;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetParaVisitor;
import net.sourceforge.czt.circus.visitor.TransformerParaVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UndeterminedTypeException;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.visitor.ParaVisitor;

/**
 * <p>
 * This visitor is used to build up a basic process signature.
 * It is called within the {@link #ProcessChecker.visitZParaList(Term)} method.
 * The protocol fill the basic process signature that was set at the beginning.
 * The resulting signature is used by the ProcessParaChecker to do post checking,
 * which resolve mutually recursive calls.
 * </p>
 * <p>
 * It must implement all elements that are part of a basic process signature.
 * That is, all elements that satisfy {@link #CircusUtils.isCircusInnerProcessPara(Para)}. 
 * </p>
 * 
 * @author leo
 */
public class BasicProcessChecker extends Checker<Signature>
  implements
  ParaVisitor<Signature>,
  ActionParaVisitor<Signature>,
  NameSetParaVisitor<Signature>,
  TransformerParaVisitor<Signature>
{

  private boolean processedState_;
  private BasicProcessSignature basicProcessSig_;

  public BasicProcessChecker(TypeChecker tc)
  {
    super(tc);
    setCurrentBasicProcessSignature(null);
  }
              
  /**
   * Sets the current basic process signature being filled as a result of 
   * the processing of the BasicProcess in ProcessParaChecker. It also clears
   * the flag (i.e. set it to false) determining whether or not the process state
   * has already been processed or not.
   * @param sig
   */
  protected void setCurrentBasicProcessSignature(BasicProcessSignature sig)
  {
    basicProcessSig_ = sig;
    processedState_ = false;
  }
  
  protected BasicProcessSignature getCurrentBasicProcesssignature()
  {
    return basicProcessSig_;
  }
  
  /**
   * <p>
   * Processes the given term and corresponding (checked) signature
   * as the basci process state paragraph. As the parser allows various
   * kinds of paragraph for the state, we process the here.
   * </p>
   * <p>
   * The precondition for this method is that: the given Para term is one
   * of the allowed Para for process state; the given signature contains at 
   * least one element (the first element) that is a reference to a SchemaType;
   * and the state cannot be processed more than once.
   * </p>
   * @param term
   * @param paraSig
   */
  protected void processStatePara(Para term, Signature paraSig)
  {    
    assert CircusUtils.isStatePara(term) &&
           !paraSig.getNameTypePair().isEmpty() : "invalid state paragraph";
    
    SchemaType type = referenceToSchema(paraSig.getNameTypePair().get(0).getType());    
    
    if (type == null)
    {
      throw new UndeterminedTypeException("Invalid state paragraph. It is not of SchemaType");
    }
    else if (!processedState_)
    {
      // TODO:? unify paraSig with term's? nah. leave it
      paraSig = addStateVars(type);
      basicProcessSig_.setStateSignature(paraSig);
      processedState_ = true;
    }
    else
    { 
      String position = position(term);
      logger().warning(getClass().getName() +
        " being asked to process state paragraph twice " +
        " at location " + position); 
    }
  }
  
  protected void raiseBasicProcessParaTypeError(Para term, String expected, Type2 found)
  {  
    Object[] params = { getCurrentProcessName(), 
       getConcreteSyntaxSymbol(term), expected, found };      
    error(term, ErrorMessage.BASIC_PROCESS_PARA_WRONG_TYPE, params);
  }

  public Signature visitPara(Para term)
  {
    assert getCurrentBasicProcess() != null && getCurrentBasicProcesssignature() != null;
    
    // Leave this assertion out. If not processed, the checker will get it anyway.      
    //assert ZUtils.isZPara(term) || GlobalDefs.isIgnorePara(term) : 
    //  "invalid Z paragraph within process " + getCurrentProcessName();
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());                
    
    // for the process state, add local variables to the process global scope    
    if (CircusUtils.isStatePara(term))
    {
      processStatePara(term, paraSig);      
    } 
    else
    {
      basicProcessSig_.getLocalZSignatures().add(paraSig);
    }
    return paraSig;
  }

  @Override
  public Signature visitActionPara(ActionPara term)
  {
    assert getCurrentBasicProcess() != null && getCurrentBasicProcesssignature() != null;
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());            
    assert paraSig.getNameTypePair().size() == 1 : 
      "too many pairs in process para checker signature result";
          
    // for the process state, add local variables to the process global scope    
    if (CircusUtils.isStatePara(term))
    {
      processStatePara(term, paraSig);      
    }    
    else 
    {      
      Type2 type = getType2FromAnns(term.getCircusAction());
      if (type instanceof ActionType)
      {   
        // TODO:? unify paraSig with term's? nah. leave it
        basicProcessSig_.getActionSignatures().add(
          GlobalDefs.actionType(type).getActionSignature());
      }
      else
      {        
        raiseBasicProcessParaTypeError(term, "ActionType", type);
      }
    }
    // for action para this will contain one element with the action name.
    return paraSig;
  }  
  
  @Override
  public Signature visitNameSetPara(NameSetPara term)
  {
    assert getCurrentBasicProcess() != null && getCurrentBasicProcesssignature() != null;
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());                
    assert paraSig.getNameTypePair().size() == 1 : 
      "too many pairs in process para checker signature result";
            
    Type2 type = getType2FromAnns(term.getNameSet());
    if (type instanceof NameSetType)
    {   
      // TODO:? unify paraSig with term's? nah. leave it
      basicProcessSig_.getUsedNameSets().getNameTypePair().addAll(paraSig.getNameTypePair());
      //  .getSignature());
    }
    else
    {        
      raiseBasicProcessParaTypeError(term, "NameSetType", type);
    }    
    return paraSig;
  }

  @Override
  public Signature visitTransformerPara(TransformerPara term)
  {
    assert getCurrentBasicProcess() != null && getCurrentBasicProcesssignature() != null;
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());            
    
    // should have only one pair in paraSig, but use a loop in case 
    // other transformers are added.
    for(NameTypePair pair : paraSig.getNameTypePair())
    {
      basicProcessSig_.getTransformerParaName().add(pair.getZName());
    }    
    return paraSig;
  }
}
