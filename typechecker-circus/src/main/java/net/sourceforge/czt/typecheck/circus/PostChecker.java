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
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.ParameterAnn;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;

/**
 * <p>
 * At the end of the typechecker, this checker visits any previously
 * unresolved SetExprs and RefExprs (expressions that may introduce a
 * variable type into their type) to ensure that all implicit
 * parameters have been determined.
 * </p>
 * <p>
 * In Circus, due to the presence of mutually recurisve calls,
 * we also have post checking for action and process calls. 
 * </p>
 */
public class PostChecker
  extends Checker<net.sourceforge.czt.typecheck.z.ErrorAnn>
implements //CallProcessVisitor<net.sourceforge.czt.typecheck.z.ErrorAnn>,
  CallActionVisitor<net.sourceforge.czt.typecheck.z.ErrorAnn>
{

  protected net.sourceforge.czt.typecheck.z.PostChecker zPostChecker_;

  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPostChecker_ =
      new net.sourceforge.czt.typecheck.z.PostChecker(typeChecker);
  }

  public net.sourceforge.czt.typecheck.z.ErrorAnn visitTerm(Term term)
  {
    return term.accept(zPostChecker_);
  }
//
//  public net.sourceforge.czt.typecheck.z.ErrorAnn visitCallProcess(CallProcess term)
//  {
//    ZRefName procRef = assertZRefName(term.getRefName());
//    ZDeclName procDecl = factory().createZDeclName(procRef);
//    net.sourceforge.czt.typecheck.z.ErrorAnn errorAnn = null;
//    if (!isProcess(procDecl))
//    {
//      Object[] params = {assertZDeclName(currentProcess()).getWord(),
//        procDecl.getWord()
//      };
//      errorAnn = errorAnn(term, ErrorMessage.IS_NOT_PROCESS_NAME, params);
//    }
//    else
//    {
//      ProcessType procType = (ProcessType) sectTypeEnv().getType(procRef);
//      ProcessSignature procSignature = procType.getProcessSignature();
//      setCurrentProcess(procSignature.getProcessName());
//      List<NameTypePair> paramsOrIndexes = null;
//      if (procSignature.getParamsOrIndexes() != null)
//      {
//        paramsOrIndexes = procSignature.getParamsOrIndexes().getNameTypePair();
//      }
//      // chama um método auxiliar que irá verificar se a chamada está correta
//      errorAnn = checkCallProcess(term, paramsOrIndexes);
//    }
//    return errorAnn;
//  }
//
  
  @Override
  public net.sourceforge.czt.typecheck.z.ErrorAnn visitCallAction(CallAction term)
  {    
    assert isWithinProcessParaScope() : "Action post checking requires process scope";
    
    boolean added;
    net.sourceforge.czt.typecheck.z.ErrorAnn result;
    ZName zName = term.getZName();
    UndeclaredAnn uAnn = zName.getAnn(UndeclaredAnn.class);
    final boolean nameIsUndeclared = uAnn != null;
    if (nameIsUndeclared) 
    {            
      result = createUndeclaredNameError(zName);
      GlobalDefs.removeAnn(zName, uAnn);      
      added = addErrorAnn(term, result);
    }
    else
    {
      Type type = getType(zName);
      List<ErrorAnn> callErrors = checkCallActionConsistency(GlobalDefs.unwrapType(type), term);      
      
      // add the errors to all terms.
      added = false;
      result = null;
      for(ErrorAnn e : callErrors)
      {
        boolean r = addErrorAnn(term, e);
        added = added || r;
      }
      
      // accumulate all post check errors at once.
      if (added)
      {        
        Object[] params = { getCurrentProcessName(), getConcreteSyntaxSymbol(term), term, callErrors.size() };
        result = errorAnn(term, ErrorMessage.POSTCHECKING_CALL_ERROR, params);
        // cast it as a Circus ErrorAnn
        ((ErrorAnn)result).addCallErrors(callErrors);
      }
    }      
    return added ? result : null;
  }
  
//
//  // TODO: Check: it seems a bug here because the received parameter is assigned inside this method.
//  //              this does not come out in the result. That is the assignments on the parameter errorann is lost!!!
//  //              For this effect what you need is an attribute.
//  //
//  // Ex: try 
//  //  static void m(Integer i) {
//  //      i = new Integer(10);
//  //  }
//  //  static void main(String[]) {
//  //      Integer x = new Integer(0);
//  //      m(x);
//  //      // It is 0, and not 10!
//  //      System.out.prinln(x);
//  //  }
//  //
//  // TODO: Checked that checkCallProc here and checkCall in ProcessChecker are mostly the same. the difference is 
//  //       just at the errorAnn(...) rather than error(...) method call. Could be refactored to go to the Checker class.
//  private net.sourceforge.czt.typecheck.z.ErrorAnn checkCallProcessParamTypes(ZDeclName procName,
//    List<NameTypePair> decs, List<Type2> types)
//  {
//    // TODO: Check the relevance of this boolean returned value. It seems irrelevant for your checking purposes.
//    //     at least it is not being used anywhere!.
//    //boolean result = true;
//    net.sourceforge.czt.typecheck.z.ErrorAnn errorAnn = null;
//    int i = 0;
//    if (decs.size() == types.size())
//    {
//      for (NameTypePair pair : decs)
//      {
//        Type2 expectedU = unwrapType(pair.getType());
//        Type2 foundU = unwrapType(types.get(i));
//        if (foundU instanceof UnknownType)
//        {
//          Object[] params = {assertZDeclName(currentProcess()).getWord(),
//            procName.getWord(), i + 1
//          };
//          errorAnn = errorAnn(procName,
//            ErrorMessage.PARAM_PROC_CALL_UNDECLARED_VAR, params);
//          //result = false;
//          break;
//        }
//        if (unify(foundU, expectedU) != SUCC)
//        {
//          Object[] params = {assertZDeclName(currentProcess()).getWord(),
//            expectedU, foundU, i, procName.getWord()
//          };
//          errorAnn = errorAnn(procName, ErrorMessage.PARAM_PROC_CALL_NOT_UNIFY,
//            params);
//          //result = false;
//          break;
//        }
//        i++;
//      }
//    }
//    else
//    {
//      Object[] params = {assertZDeclName(currentProcess()).getWord(),
//        decs.size(), types.size(), procName.getWord()
//      };
//      errorAnn = errorAnn(procName, ErrorMessage.PROC_CALL_DIFF_NUMBER_EXPRS,
//        params);
//    //result = false;
//    }
//
//    // return result;
//    return errorAnn;
//  }
//
//  // TODO: This is nearly the same as the one in ProcessChecker, where the difference is that
//  //       it returns an ErrorAnn! Maybe put in GlobalDefs or in Checker?
//  // TODO: Checked that checkCallProc here and checkCall in ProcessChecker are mostly the same. the difference is 
//  //       just at the errorAnn(...) rather than error(...) method call. Refactored to go to the Checker class.
//  private net.sourceforge.czt.typecheck.z.ErrorAnn checkCallProcess(CallProcess term,
//    List<NameTypePair> paramsOrIndexes)
//  {
//    ZDeclName procDecl = factory().createZDeclName(assertZRefName(term.getRefName()));
//    String kindOfProcess = getKindOfProcess(procDecl);
//    List<Type2> typeExprs = new ArrayList<Type2>();
//    ZExprList exprs = null;
//    net.sourceforge.czt.typecheck.z.ErrorAnn errorAnn = null;
//
//    // TODO: Check: why do you use kindOfProcess for Param e Index but not Generic? 
//    //              why is kindOfProcess necessary?
//
//    // TODO: Check this comment. Old CallType.Gen, GenParam, GenIndex.
//    //
//    //  Regardless the indexes or the parameters, generics must always be checked.       
//    ZExprList zGenActuals = term.getGenActuals() == null ? null : assertZExprList(term.getGenActuals());
//    if (zGenActuals != null && !zGenActuals.isEmpty())
//    {
//      if (!isGenericProcess(procDecl))
//      {
//        Object[] params = {assertZDeclName(currentProcess()).getWord(),
//          procDecl.getWord()
//        };
//        errorAnn = errorAnn(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL,
//          params);
//      }
//      else
//      {
//        ZExprList genExprs = zGenActuals;
//        List<Type2> typeGenExprs = new ArrayList<Type2>();
//        for (Expr genExpr : genExprs)
//        {
//          Type2 type = genExpr.accept(exprChecker());
//          typeGenExprs.add(type);
//        }
//        List<DeclName> genParams = getGenParamsProcess(procDecl);
//        if (genParams.size() != typeGenExprs.size())
//        {
//          Object[] params = {assertZDeclName(currentProcess()).getWord(),
//            procDecl.getWord(),
//            genParams.size(), typeGenExprs.size()
//          };
//          errorAnn = errorAnn(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR,
//            params);
//        }
//      }
//    }
//    // Now we check if the parameters are to be considered or not.
//    // CallType.Normal!
//    ZExprList zActuals = term.getActuals() == null ? null : assertZExprList(term.getActuals());
//    if (zActuals == null || zActuals.isEmpty())
//    {
//      if (!kindOfProcess.equals("NORMAL"))
//      {
//        Object[] params = {assertZDeclName(currentProcess()).getWord(),
//          procDecl.getWord()
//        };
//        errorAnn = errorAnn(term, ErrorMessage.PROC_CALL_NEEDS_PARAMS, params);
//      }
//    }
//    // CallType.Param, CallType.Index
//    else
//    {
//      assert zActuals != null && !zActuals.isEmpty();
//      if (term.getCallType().equals(CallType.Param))
//      {
//        if (!kindOfProcess.equals("PARAM"))
//        {
//          Object[] params = {assertZDeclName(currentProcess()).getWord(),
//            procDecl.getWord()
//          };
//          errorAnn = errorAnn(term,
//            ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
//        }
//        else
//        {
//          exprs = zActuals;
//          for (Expr expr : exprs)
//          {
//            Type2 type = expr.accept(exprChecker());
//            typeExprs.add(type);
//          }
//          errorAnn = checkCallProcessParamTypes(procDecl, paramsOrIndexes,
//            typeExprs);
//        }
//      }
//      else
//      {
//        if (!kindOfProcess.equals("INDEX"))
//        {
//          Object[] params = {assertZDeclName(currentProcess()).getWord(),
//            procDecl.getWord()
//          };
//          errorAnn = errorAnn(term,
//            ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
//        }
//        else
//        {
//          // TODO: Check if here is actuals or not.
//          exprs = zActuals;
//          for (Expr expr : exprs)
//          {
//            Type2 type = expr.accept(exprChecker());
//            typeExprs.add(type);
//          }
//          errorAnn = checkCallProcessParamTypes(procDecl, paramsOrIndexes,
//            typeExprs);
//        }
//      }
//    }
//
//    /*
//    switch(term.getCallType()) {
//    case Param :
//    if(!kindOfProcess.equals("PARAM")){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
//    }
//    else {
//    // TODO: Check if here is actuals or not.
//    exprs = assertZExprList(term.getActuals());
//    for(Expr expr : exprs) {
//    Type2 type = expr.accept(exprChecker());
//    typeExprs.add(type);
//    }
//    checkCallProc(procDecl, paramsOrIndexes, typeExprs, errorAnn);
//    }
//    break;
//    case Index :
//    if(!kindOfProcess.equals("INDEX")){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
//    }
//    else {
//    // TODO: Check if here is actuals or not.
//    exprs = assertZExprList(term.getActuals());
//    for(Expr expr : exprs) {
//    Type2 type = expr.accept(exprChecker());
//    typeExprs.add(type);
//    }
//    checkCallProc(procDecl, paramsOrIndexes, typeExprs, errorAnn);
//    }
//    break;
//    case Gen :
//    if(!isGenericProcess(procDecl)){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
//    }
//    else {
//    // TODO: Check if here is genActuals or not.
//    exprs = assertZExprList(term.getGenActuals());
//    for(Expr expr : exprs) {
//    Type2 type = expr.accept(exprChecker());
//    if(!(type instanceof PowerType)) {
//    // ERRO. A EXPRESSÃO DEVE SER UM CONJUNTO
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_POWER_TYPE_IN_GEN_PROCESS, params);
//    break;
//    }
//    else {
//    typeExprs.add(type);
//    }
//    }
//    List<DeclName> genParams = getGenParamsProcess(procDecl);
//    if(genParams.size() != typeExprs.size()) {
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
//    genParams.size(), typeExprs.size()};
//    errorAnn = errorAnn(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
//    }
//    }
//    break;
//    case GenParam :
//    if(!isGenericProcess(procDecl)){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
//    }
//    else {
//    // TODO: Check if here is genActuals or not.
//    ZExprList genExprs = assertZExprList(term.getGenActuals());
//    List<Type2> typeGenExprs = new ArrayList<Type2>();
//    for(Expr genExpr : genExprs) {
//    Type2 type = genExpr.accept(exprChecker());
//    typeGenExprs.add(type);
//    }
//    List<DeclName> genParams = getGenParamsProcess(procDecl);
//    if(genParams.size() != typeGenExprs.size()) {
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
//    genParams.size(), typeGenExprs.size()};
//    errorAnn = errorAnn(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
//    }
//    if(!kindOfProcess.equals("PARAM")){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL, params);
//    }
//    else {
//    // TODO: Check if here is actuals or not. 
//    exprs = assertZExprList(term.getActuals());
//    for(Expr expr : exprs) {
//    Type2 type = expr.accept(exprChecker());
//    typeExprs.add(type);
//    }
//    checkCallProc(procDecl, paramsOrIndexes, typeExprs, errorAnn);
//    }
//    }
//    break;
//    case GenIndex :
//    if(!isGenericProcess(procDecl)){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_GEN_PROCESS_IN_PROC_CALL, params);
//    }
//    else {
//    // TODO: Check if here is genActuals or not.
//    ZExprList genExprs = assertZExprList(term.getGenActuals());
//    List<Type2> typeGenExprs = new ArrayList<Type2>();
//    for(Expr genExpr : genExprs) {
//    Type2 type = genExpr.accept(exprChecker());
//    typeGenExprs.add(type);
//    }
//    List<DeclName> genParams = getGenParamsProcess(procDecl);
//    if(genParams.size() != typeGenExprs.size()) {
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord(),
//    genParams.size(), typeGenExprs.size()};
//    errorAnn = errorAnn(term, ErrorMessage.GEN_PROCESS_INSTANTIATION_ERROR, params);
//    }
//    if(!kindOfProcess.equals("INDEX")){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_INDEX_PROCESS_IN_PROC_CALL, params);
//    }
//    else {
//    // TODO: Check if here is actuals or not.
//    exprs = assertZExprList(term.getActuals());
//    for(Expr expr : exprs) {
//    Type2 type = expr.accept(exprChecker());
//    typeExprs.add(type);
//    }
//    checkCallProc(procDecl, paramsOrIndexes, typeExprs, errorAnn);
//    }
//    }
//    break;
//    case Normal :
//    if(!kindOfProcess.equals("NORMAL")){
//    Object [] params = {assertZDeclName(currentProcess()).getWord(), procDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.PROC_CALL_NEEDS_PARAMS, params);
//    }
//    break;
//    }
//     */
//    return errorAnn;
//  }
//
//  private net.sourceforge.czt.typecheck.z.ErrorAnn checkCallAction(CallAction term,
//    List<NameTypePair> params)
//  {
//
//    ZDeclName actionDecl = factory().createZDeclName(assertZRefName(term.getRefName()));
//    net.sourceforge.czt.typecheck.z.ErrorAnn errorAnn = null;
//
//    // TODO: Check this comment.
//    // CallType.Param
//    if (!term.getZExprList().isEmpty())
//    {
//      if (!localCircTypeEnv().isParamAction(actionDecl))
//      {
//        Object[] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).
//          getWord(), actionDecl.getWord()
//        };
//        errorAnn = errorAnn(term,
//          ErrorMessage.IS_NOT_PARAM_ACTION_IN_ACTION_CALL, paramsError);
//      }
//      else
//      {
//        List<Type2> typeExprs = new ArrayList<Type2>();
//        ZExprList exprs = term.getZExprList();
//        for (Expr expr : exprs)
//        {
//          Type2 type = expr.accept(exprChecker());
//          typeExprs.add(type);
//        }
////
//        // TODO: Just for uniformity, everywhere (in ActionChecker, ProcessChecker, and Here), 
//        //       you use an auxiliary method for this check. The code is therefore copied
//        //       in at least four different places! If you find a bug later on, this becomes 
//        //       nightmare!!! 
//        int i = 0;
//        if (params.size() == typeExprs.size())
//        {
//          for (NameTypePair pair : (List<NameTypePair>) params)
//          {
//            Type2 expectedU = unwrapType(pair.getType());
//            Type2 foundU = unwrapType(typeExprs.get(i));
//            if (foundU instanceof UnknownType)
//            {
//              Object[] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).
//                getWord(), actionDecl.getWord(), i + 1
//              };
//              errorAnn = errorAnn(actionDecl,
//                ErrorMessage.PARAM_ACTION_CALL_UNDECLARED_VAR, paramsError);
//              break;
//            }
//            if (unify(foundU, expectedU) != SUCC)
//            {
//              Object[] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).
//                getWord(), actionDecl.getWord(), expectedU, foundU, i + 1
//              };
//              errorAnn = errorAnn(actionDecl,
//                ErrorMessage.PARAM_ACTION_CALL_NOT_UNIFY, paramsError);
//              break;
//            }
//            i++;
//          }
//        }
//        else
//        {
//          Object[] paramsError = {params.size(), typeExprs.size(),
//            actionDecl.getWord()
//          };
//          errorAnn = errorAnn(actionDecl,
//            ErrorMessage.ACTION_CALL_DIFF_NUMBER_EXPRS, paramsError);
//        }
//      }
//    }
//    // CallType.Normal
//    else
//    {
//      if (localCircTypeEnv().isParamAction(actionDecl))
//      {
//        Object[] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).
//          getWord(), actionDecl.getWord()
//        };
//        errorAnn = errorAnn(term, ErrorMessage.PARAM_ACTION_CALL_WITHOUT_EXPRS,
//          paramsError);
//      }
//    }
//    /*
//    switch(term.getCallType()) {
//    case Param :
//    if(!localCircTypeEnv().isParamAction(actionDecl)){
//    Object [] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), actionDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.IS_NOT_PARAM_ACTION_IN_ACTION_CALL, paramsError);
//    }
//    else {
//    List<Type2> typeExprs = new ArrayList<Type2>();
//    ZExprList exprs = term.getZExprList();
//    for(Expr expr : exprs) {
//    Type2 type = expr.accept(exprChecker());
//    typeExprs.add(type);
//    }
//    //
//    int i = 0;
//    if(params.size() == typeExprs.size()) {
//    for(NameTypePair pair : (List<NameTypePair>)params) {
//    Type2 expectedU = unwrapType(pair.getType());
//    Type2 foundU = unwrapType((Type)typeExprs.get(i));
//    if(foundU instanceof UnknownType) {
//    Object [] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), actionDecl.getWord(), i+1};
//    errorAnn = errorAnn(actionDecl, ErrorMessage.PARAM_ACTION_CALL_UNDECLARED_VAR, paramsError);
//    break;
//    }
//    if(unify(foundU, expectedU) != SUCC) {
//    Object [] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), actionDecl.getWord(), expectedU, foundU, i+1};
//    errorAnn = errorAnn(actionDecl, ErrorMessage.PARAM_ACTION_CALL_NOT_UNIFY, paramsError);
//    break;
//    }   
//    i++;
//    }
//    } else {
//    Object [] paramsError = {params.size(), typeExprs.size(), actionDecl.getWord()};
//    errorAnn = errorAnn(actionDecl, ErrorMessage.ACTION_CALL_DIFF_NUMBER_EXPRS, paramsError);
//    }
//    //
//    }
//    break;
//    case Normal :
//    if(localCircTypeEnv().isParamAction(actionDecl)) {
//    Object [] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), actionDecl.getWord()};
//    errorAnn = errorAnn(term, ErrorMessage.PARAM_ACTION_CALL_WITHOUT_EXPRS, paramsError);
//    }
//    break;
//    }
//     */
//    return errorAnn;
//  }
}
