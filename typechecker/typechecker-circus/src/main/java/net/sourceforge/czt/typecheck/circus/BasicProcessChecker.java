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
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetParaVisitor;
import net.sourceforge.czt.circus.visitor.TransformerParaVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.SignatureAnn;
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
public class BasicProcessChecker extends Checker<CircusCommunicationList>
  implements
  ParaVisitor<CircusCommunicationList>,
  ActionParaVisitor<CircusCommunicationList>,
  NameSetParaVisitor<CircusCommunicationList>,
  TransformerParaVisitor<CircusCommunicationList>
{

  private boolean processedState_;
  private ProcessSignature basicProcessSig_;

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
  protected ProcessSignature setCurrentBasicProcessSignature(ProcessSignature sig)
  {
    ProcessSignature old = basicProcessSig_;
    basicProcessSig_ = sig;
    processedState_ = false;
    return old;
  }
  
  protected ProcessSignature getCurrentBasicProcesssignature()
  {
    return basicProcessSig_;
  }
  
  protected void checkBPSignature(Object term)
  {
    // we could have compound basic processes, such as tc327\_intchoice\_bp
    assert /*getCurrentBasicProcess() != null &&*/ getCurrentBasicProcesssignature() != null
      : "null basic process signature whilst visiting " + term.getClass().getSimpleName();
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
  private Signature processStatePara(Para term, Signature paraSig)
  {    
    assert CircusUtils.isStatePara(term) && !paraSig.getNameTypePair().isEmpty() : "invalid state paragraph";
    
    Signature result;
    SchemaType type = referenceToSchema(paraSig.getNameTypePair().get(0).getType());    
    
    if (type == null)
    {
      result = basicProcessSig_.getStateSignature();
      warningManager().warn("Invalid state paragraph. It is not of SchemaType. " +
        "This is a inconsistency problem and shouldn't happen. Please, report.");
    }
    else if (!processedState_)
    {
      // TODO:? unify paraSig with term's? nah. leave it
      result = addStateVars(type);
      basicProcessSig_.setStateSignature(paraSig);
      processedState_ = true;
    }
    else
    { 
      result = basicProcessSig_.getStateSignature();
      assert result != null : "invalid state signature for basic process";      
      warningManager().warn(term, WarningMessage.DUPLICATED_PROCESS_STATE, 
        getCurrentProcessName(), getConcreteSyntaxSymbol(term));
    }
    
    return result;
  }
  
  private void raiseBasicProcessParaTypeError(Para term, String expected, Type2 found)
  {  
    Object[] params = { getCurrentProcessName(), 
       getConcreteSyntaxSymbol(term), expected, found };      
    error(term, ErrorMessage.BASIC_PROCESS_PARA_WRONG_TYPE, params);
  }
  
  public CircusCommunicationList visitPara(Para term)
  {
    checkBPSignature(term);
    
    // Leave this assertion out. If not processed, the checker will get it anyway.      
    //assert ZUtils.isZPara(term) || GlobalDefs.isIgnorePara(term) : 
    //  "invalid Z paragraph within process " + getCurrentProcessName();
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());                
    
    // for the process state not declared as an action, 
    // add local variables to the process global scope    
    if (CircusUtils.isStatePara(term))
    {
      paraSig = processStatePara(term, paraSig);      
      
      // as the signature will change, update it accordingly      
      GlobalDefs.removeAnn(term, SignatureAnn.class);
      addSignatureAnn(term, paraSig);      
    } 
    else 
    {
      basicProcessSig_.getBasicProcessLocalZSignatures().add(paraSig);
    }
    
    // added by ParaChecker within ProcessParaChecker
    // addSignatureAnn(term, paraSig);    
    return factory().createEmptyCircusCommunicationList();
  }

  @Override
  public CircusCommunicationList visitActionPara(ActionPara term)
  {
    checkBPSignature(term);
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());            
    assert paraSig.getNameTypePair().size() == 1 : 
      "too many pairs in process para checker signature result";          

    CircusCommunicationList commList = factory().createEmptyCircusCommunicationList();
    
    Type2 type = getType2FromAnns(term);
    if (type instanceof ActionType)
    {   
      ActionType aType = (ActionType)type;
      CircusCommunicationList actionComms = factory().deepCloneTerm(
        aType.getActionSignature().getUsedCommunications());
      commList.addAll(actionComms);
      
      // get the action signature for this basic process
      // TODO:? unify paraSig with term's? nah. leave it
      basicProcessSig_.getActionSignatures().add(
        aType.getActionSignature());
    }
    else
    {        
      raiseBasicProcessParaTypeError(term, "ActionType", type);
    }
    
    // for action para this will contain one element with the action name.
    //addSignatureAnn(term, paraSig);
    
    return commList;
  }  
  
  @Override
  public CircusCommunicationList visitNameSetPara(NameSetPara term)
  {
    checkBPSignature(term);
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());                
    assert paraSig.getNameTypePair().size() == 1 : 
      "too many pairs in process para checker signature result";

    // get the typechecked name set from annotations
    Type2 type = getType2FromAnns(term);

    // unwrap it from its power type
    Type2 innerType = type;
    if (type instanceof PowerType)
    {
      innerType = GlobalDefs.powerType(type).getType();
    }

    // if of the right kind, add to the basic process signature
    if (innerType instanceof NameSetType)
    { 
      // TODO:? unify paraSig with term's? leave it for now.
      basicProcessSig_.getBasicProcessLocalZSignatures().add(paraSig);      
    }
    // raise a basic process level error otherwise.
    else
    {        
      raiseBasicProcessParaTypeError(term, "NameSetType", innerType);
    }    
    
    //addSignatureAnn(term, paraSig);
    return factory().createEmptyCircusCommunicationList();
  }

  @Override
  public CircusCommunicationList visitTransformerPara(TransformerPara term)
  {
    checkBPSignature(term);
    
    // type check the  process paragraph
    Signature paraSig = term.accept(processParaChecker());                
    assert paraSig.getNameTypePair().size() == 1 : 
      "too many pairs in process para checker signature result";
            
    Type2 type = getType2FromAnns(term);
    if (((ParaChecker)paraChecker()).transformerType().getClass().isInstance(type))
    { 
      // TODO:? unify paraSig with term's? nah. leave it
      basicProcessSig_.getBasicProcessLocalZSignatures().add(paraSig);            
    }
    else
    {        
      raiseBasicProcessParaTypeError(term, "transformer pred type", type);
    }    
    
    // added by ParaChecker, which is called within ProcessParaChecker
    // addSignatureAnn(term, paraSig);
    return factory().createEmptyCircusCommunicationList();
  }
}
