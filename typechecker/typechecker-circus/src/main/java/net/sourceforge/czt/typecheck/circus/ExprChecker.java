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

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.BasicChannelSetExpr;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusChannelSet;
import net.sourceforge.czt.circus.ast.CircusType;
import net.sourceforge.czt.circus.ast.SigmaExpr;
import net.sourceforge.czt.circus.ast.CircusNameSet;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.visitor.BasicChannelSetExprVisitor;
import net.sourceforge.czt.circus.visitor.CircusChannelSetVisitor;
import net.sourceforge.czt.circus.visitor.CircusNameSetVisitor;
import net.sourceforge.czt.circus.visitor.SigmaExprVisitor;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.SetExprVisitor;

/**
 * Visitor that checks Circus expressions. They are channel set display expressions,
 * and sigma expressions, which represent channel selection like "c.1" or "c.true".
 *
 * @author Leo Freitas
 */
public class ExprChecker
  extends Checker<Type2>
  implements 
    BasicChannelSetExprVisitor<Type2>,  // C.5.1, C.5.2
    CircusChannelSetVisitor<Type2>,     // C.5.1, C.5.2, C.5.3, C.5.4, C.5.5, C.5.6 
    SetExprVisitor<Type2>,              // C.9.1, C.9.2 - inner expressions    
    CircusNameSetVisitor<Type2>,        // C.9.1, C.9.2, C.9.3, C.9.4, C.9.5, C.9.6    
    SigmaExprVisitor<Type2>
{  
  
  /**
   * Flag whether checking name set expressions or not.
   */
  private boolean isWithinNameSet_;
  private boolean isWithinChannelSet_;                  
  
  protected boolean inProcessPara_;
  protected boolean inActionPara_;
  protected boolean inNameSetPara_;
  protected boolean inChannelSetPara_;
  
  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.ExprChecker zExprChecker_;

  public ExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    resetFlags();
    zExprChecker_ = new net.sourceforge.czt.typecheck.z.ExprChecker(typeChecker);    
  }
  
  private void resetFlags()
  {
    isWithinNameSet_ = false;
    isWithinChannelSet_ = false;
    inProcessPara_ = false;
    inActionPara_ = false;
    inNameSetPara_ = false;
    inChannelSetPara_ = false;
  }

  /**
   * For all other expression terms, use the standard Z typechecking rules 
   * within the checking environment for Circus. This also includes expression lists.
   *   
   * @law C.18.1, C.18.2, C.18.5, C.18.7
   * @law C.9.3, C.9.4, C.9.5, C.9.6 - for inner expressions
   */
  @Override
  public Type2 visitTerm(Term term)
  {
    return term.accept(zExprChecker_);
  } 
  
  /**
   * For ApplExpr, we only need to care if the underlying term is within either 
   * a channel set display expression (e.g., in a parallel or hiding operator,
   * or within a channel set paragraph). For example: CS == CS0 \\cup \\lchanset d \\rchanset,
   * or P \\lpar CS \\up CS2 \\rpar Q.
   *
   * Otherwise, we just use the zExprChecker_ for Z expressions instead.
   *
   * = this takes place in the UnificationEnv for ChannelSetType and NameSetType. 
   * 
   * @param term
   * @return
   */
  //@Override
  //public Type2 visitApplExpr(ApplExpr term)
  

  /**
   * The type of channel set displays is a signature containing name-type 
   * pairs of each channel element within the display. So, for example, 
   * if we had a display like \{| x, y.0 |\} for channels "x: \num; y: \nat",
   * the resulting signature would be "\lblot x: \num; y: \num \rblot", and 
   * hence the resulting type is 
   * <br>
   * POWER_TYPE(CHANNELSET_TYPE(SIGNATURE(<(x,POWER_TYPE(\arithmos)), (y, POWER_TYPE(\arithmos))>)))   * 
   * 
   * @law C.5.1, C.5.2
   */
  @Override
  public Type2 visitBasicChannelSetExpr(BasicChannelSetExpr term)
  {    
    assert isWithinChannelSet_ : "cannot check basic channel set expressions outside channelsets.";
    
    // check all communications within the channel set display
    List<NameTypePair> pairs = term.getCommunicationList().accept(commChecker());

    // avoid duplicates    
    checkForDuplicateNames(pairs, term);
    
    int i = 1;
    for(NameTypePair pair : pairs)
    {
      //System.out.println("Basic CS with channel " + pair.getName() + " : " + pair.getType());
      if (!(GlobalDefs.unwrapType(pair.getType()) instanceof ChannelType))
      {
        List<Object> params = factory().list();    
        params.add((inProcessPara_ ? "process" : 
          (inActionPara_ ? "action" : 
          (inChannelSetPara_ ? "channel set" : "???"))));
        params.add((inActionPara_ ? 
          (getCurrentProcessName().toString() + "\n\tAction...:" +
           getCurrentActionName().toString()) :
          (inProcessPara_ ? getCurrentProcessName() :
              (inChannelSetPara_ ? getCurrentChannelSetName() : "error"))));
        params.add(pair.getName() + ": " + pair.getType());
        params.add(i);
        error(term, ErrorMessage.NON_CHANNELSET_IN_COMMLIST, params);                
      }
      i++;
    }
    
    // create channel set type with the found pairs as its signature
    Signature channelSetSig = factory().createSignature(pairs);
    ChannelSetType cstype = factory().createChannelSetType(channelSetSig);

    // create product type of the collected channel set type as the result.
    PowerType result = factory().createPowerType(cstype);
    addTypeAnn(term, result);

    return result;
  }
  
  /**
   * 
   * @param term
   * @return
   * @law C.5.1, C.5.2, C.5.3, C.5.4, C.5.5, C.5.6 
   */
  @Override
  public Type2 visitCircusChannelSet(CircusChannelSet term)
  {
    // channel sets must be either within a NameSetPara 
    // (when declared) or an ActionPara (when used).
    checkChannelSetScope(term);
    
    // flag we are checking a nameset expression
    isWithinChannelSet_ = true;    
    inProcessPara_ = isWithinProcessParaScope();
    inActionPara_ = isWithinActionParaScope();
    inChannelSetPara_ = isWithinChannelSetParaScope();
    
    // typecheck all the elements using Z typechecker 
    Expr csExpr = term.getExpr();    
    Type2 innerType = factory().createUnknownType();
    Type2 type = csExpr.accept(exprChecker());
    
    if (type instanceof PowerType)
    {
      innerType = GlobalDefs.powerType(type).getType();
    }
    else
    {
      List<Object> params = factory().list();
      params.add((inProcessPara_ ? "process" : (inActionPara_ ? "action" : 
        (inChannelSetPara_ ? "channel set" : "???"))));
      params.add((inActionPara_ ? 
        (getCurrentProcessName().toString() + "\n\tAction...: " +
         getCurrentActionName().toString()) :
        (inProcessPara_ ? getCurrentProcessName() :
            (inChannelSetPara_ ? getCurrentChannelSetName() : "error"))));
      params.add(csExpr);
      params.add(type);            
      error(csExpr, ErrorMessage.NON_CHANNELSET_IN_POWEREXPR, params);
    }
    
    // create a variable power type and unify it with the result found
    PowerType vPowerType = factory().createPowerType();
    UResult unified = unify(vPowerType, type);
    
    //if the expr type is not a set, raise an error
    if (!unified.equals(UResult.FAIL)) 
    {
      innerType = vPowerType.getType();
    }
    
    // if not from a name set expression, raise the error
    if (!(innerType instanceof ChannelSetType))
    {      
      List<Object> params = factory().list();      
      params.add((inProcessPara_ ? "process" : (inActionPara_ ? "action" : 
        (inChannelSetPara_ ? "channel set" : "???"))));
      params.add((inActionPara_ ? 
        (getCurrentProcessName().toString() + "\n\tAction...: " +
         getCurrentActionName().toString()) :
        (inProcessPara_ ? getCurrentProcessName() :
            (inChannelSetPara_ ? getCurrentChannelSetName() : "error"))));
      params.add(csExpr);
      params.add(type);      
      error(term, ErrorMessage.INVALID_CHANNELSET_TYPE, params);
    }      
    addTypeAnn(term, type);    
    
    // clear all flags about circus expressions
    resetFlags();
    return type;  
  }
  
  /**
   * 
   * @param term
   * @return
   * @law C.9.1, C.9.2 - inner expressions
   */
  public Type2 visitSetExpr(SetExpr term)
  {
    Type2 result;
    
    // if typechecking name sets, check each element individually
    if (isWithinNameSet_)
    { 
      // check whether it has been typechecked before - e.g., reuse of reference
      result = getType2FromAnns(term);      
      
      // if not, then typecheck it
      if (result instanceof UnknownType)
      { 
        int i = 1;
        List<NameTypePair> pairs = factory().list();
        
        // search each expression element 
        for(Expr expr : term.getZExprList())
        {
          Type2 found = expr.accept(exprChecker());

          // only RefExpr are allowed
          if (expr instanceof RefExpr)
          {
            // still we also need to make sure that they are not of any Circus
            // type (e.g., they need to be variables: global or local).
            if (!(found instanceof CircusType))
            {
              NameTypePair ntp = factory().createNameTypePair(
                ((RefExpr)expr).getName(), found);
              pairs.add(ntp);
            }
            else
            {
              List<Object> params = factory().list();
              params.add(getCurrentProcessName());
              params.add((inActionPara_ ? "action" : (inNameSetPara_ ? "name set" : "???")));
              params.add((inActionPara_ ? getCurrentActionName() :
                (inNameSetPara_ ? getCurrentNameSetName() : "error")));
              params.add(expr);
              params.add(i);
              String clsName = found.getClass().getName();
              params.add(clsName.substring(clsName.lastIndexOf('.')+1));
              params.add(found);              
              error(term, ErrorMessage.INVALID_TYPE_IN_NAMESET_EXPR, params);
            }
          }
          else
          {
            List<Object> params = factory().list();
            params.add(getCurrentProcessName());
            params.add((inActionPara_ ? "action" : (inNameSetPara_ ? "name set" : "???")));
            params.add((inActionPara_ ? getCurrentActionName() : 
              (inNameSetPara_ ? getCurrentNameSetName() : "error")));
            params.add(expr);
            params.add(i);   
            params.add(found);
            error(term, ErrorMessage.TYPE_MISMATCH_IN_NAMESET_EXPR, params);
          }
          i++;
        }
        // create a power type of the name set type. unification should 
        // sort this out nicely. For empty name sets, the pairs will be empty, fine.
        result = factory().createPowerType(factory().createNameSetType(
          factory().createSignature(pairs)));      
      }
          
      // if resulting type is not a power of a name set type, raise an error
      if (!(result instanceof PowerType) || 
          !(GlobalDefs.powerType(result).getType() instanceof NameSetType))
      {        
        List<Object> params = factory().list();   
        params.add(getCurrentProcessName());
        params.add((inActionPara_ ? "action" : (inNameSetPara_ ? "name set" : "???")));
        params.add((inActionPara_ ? getCurrentActionName() : 
          (inNameSetPara_ ? getCurrentNameSetName() : "error")));
        params.add(term);
        params.add(result);           
        error(term, ErrorMessage.NON_NAMESET_IN_SETEXPR, params);
      }
      
      // add the type annotation
      addTypeAnn(term, result);
    }
    // otherwise, just follow the Z protocol
    else
    {
      result = term.accept(zExprChecker_);
    }
    return result;
  }
  
  private boolean isEmptyCircusIdType(Type2 type)
  {
    return type.equals(typeCheckCircusIdType());
  }
 
  /**
   * 
   * @param term
   * @return
   * @law C.9.1, C.9.2, C.9.3, C.9.4, C.9.5, C.9.6 
   */
  public Type2 visitCircusNameSet(CircusNameSet term)
  {    
    // channel sets must be either within a NameSetPara 
    // (when declared) or an ActionPara (when used).
    checkNameSetScope(term);
    
    // flag we are checking a nameset expression
    isWithinNameSet_ = true;    
    inActionPara_ = isWithinActionParaScope();
    inNameSetPara_ = isWithinNameSetParaScope();
    
    // typecheck all the elements using Z typechecker 
    Expr nsExpr = term.getExpr();    
    
    // for empty set name sets, explicitly instantiate it
    if (ZUtils.isEmptySetRefExpr(nsExpr))
    {
      assert ZUtils.isRefExpr(nsExpr) 
          && ((RefExpr)nsExpr).getExplicit() != null 
          && !((RefExpr)nsExpr).getExplicit() : "Invalid implicit empty set reference expression for Circus name set.";
      ((RefExpr)nsExpr).getZExprList().add(circusIdExpr());
    }    
    
    Type2 innerType = factory().createUnknownType();
    Type2 type = nsExpr.accept(exprChecker());
    
    if (type instanceof PowerType)
    {
      if (isEmptyCircusIdType(type))
      {
        innerType = factory().createEmptyNameSetType();
        GlobalDefs.powerType(type).setType(innerType);        
      }
      else
      {
        innerType = GlobalDefs.powerType(type).getType();
      }
    }
    else
    {
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add((inActionPara_ ? "action" : (inNameSetPara_ ? "name set" : "???")));
      params.add((inActionPara_ ? getCurrentActionName() : 
        (inNameSetPara_ ? getCurrentNameSetName() : "error")));
      params.add(nsExpr);
      params.add(type);           
      error(nsExpr, ErrorMessage.NON_NAMESET_IN_SETEXPR, params);
    }
    
    // create a variable power type and unify it with the result found
    PowerType vPowerType = factory().createPowerType();
    UResult unified = unify(vPowerType, type);
    
    //if the expr type is not a set, raise an error
    if (!unified.equals(UResult.FAIL)) 
    {
      innerType = vPowerType.getType();
    }
    
    // if not from a name set expression, neither a variable type raise the error
    if (!(innerType instanceof NameSetType))
    {      
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add((inActionPara_ ? "action" : (inNameSetPara_ ? "name set" : "???")));
      params.add((inActionPara_ ? getCurrentActionName() : 
        (inNameSetPara_ ? getCurrentNameSetName() : "error")));
      params.add(nsExpr);
      params.add(type);      
      error(term, ErrorMessage.INVALID_NAMESET_TYPE, params);
    }      
    addTypeAnn(term, type);    
    
    // clear all flags about circus expressions
    resetFlags();
    return type;  
  }

  /**
   * <p>
   * A sigma expression is formed by a channel name and a communicated value.
   * For instance, if a channel is declared as "c: \nat", and latter used in
   * a communication as "c.0", the sigma expression would be formed as a tuple
   * "(c, 0)", where "c" is a RefExpr and (in this case) "0" is a NumExpr. Other
   * types would have other valued expressions, yet all channels are RefExpr.   * 
   * </p>
   *
   * <p>
   * The resulting type is a product type of the cross product of each of these
   * two maximal types. So, for our example, the result is 
   * <br>
   * POWER_TYPE(PROD_TYPE(typeOf(RefExpr("c")), typeOf(NumExpr("0")))
   * <br>
   * which is just
   * <br>
   * POWER_TYPE(PROD_TYPE(POWER_TYPE(\arithmos), POWER_TYPE(\arithmos)))
   * <br>
   * Note that both types within the type product type are unifiable with respect
   * to their maximal types (i.e. carrier sets).
   * </p>
   * 
   * <p>
   * With those two types, we perform type unification with respect to maximal
   * type checking of Z (i.e. at the level of carrier sets). This avoids type
   * inconsistencies like "c.\true". This does not avoid, for instance, known 
   * (FDR) errors like 'outside protocol', when a communicated value is outside 
   * the channel type domain. That is, it does NOT prevent, say, 
   * "c: \nat_1 ... c.0", as a type inconsistency. 
   * </p>
   *
   * <p>
   * These extra type enforcements are undecidable, and not implemented for the
   * automatic type checking procedure for Circus. For instance, the Circus model 
   * checker adds such type encompassment check as a verification condition 
   * conjectures for type correctness. Other tools that rely on communication 
   * (e.g. all tools using the CSP side of Circus), MUST provide such verification 
   * condition generation as well.
   * </p>
   */  
  public Type2 visitSigmaExpr(SigmaExpr term)
  {
//    // check both the channel and the value types within the SigmaExpr
//    Type2 channelType = term.getChannel().accept(exprChecker());
//    Type2 valueType = term.getValue().accept(exprChecker());
//    
//    // these types MUST be unifiable, otherwise we have a communication outside
//    // its type-domain (ex: c: \nat ...   c.\true)    
//    UResult unified = unificationEnv().unify(channelType, valueType);        
//    if (unified.equals(UResult.FAIL))
//    {
//      Object [] params = {term.getChannel().toStirng(),
//        channelType.toString(), valueType.toString()};
//      error(term, ErrorMessage.CANNOT_UNIFY_SIGMAEXPR, params);
//    }    
//    Type2 result = factory().createProdType(factory().list(channelType, valueType));
//    //Type2 result = factory().createPowerType(prodType);
//    
//    addTypeAnn(term, result);
//    
//    return result;
    assert false : "TODO";
    return null;
  }
}
