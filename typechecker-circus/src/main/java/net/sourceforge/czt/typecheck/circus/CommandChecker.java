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

import net.sourceforge.czt.circus.ast.ActionSignature;


/**
 *
 * @author Leo Freitas
 * @author Manuela
 */
public class CommandChecker
  extends Checker<ActionSignature>
  /*implements //CircusCommandVisitor,
      SpecStmtCommandVisitor<ActionSignature>,      // C.17.1, C.17.4, C.17.5
      AssignmentCommandVisitor<ActionSignature>,
             
             IfGuardedCommandVisitor<ActionSignature>,
             VarDeclCommandVisitor<ActionSignature>*/
{  
  //a Z decl checker
  protected net.sourceforge.czt.typecheck.z.DeclChecker zDeclChecker_;

  /** Creates a new instance of CommandChecker */
  public CommandChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zDeclChecker_ =
      new net.sourceforge.czt.typecheck.z.DeclChecker(typeChecker);
  }
 
//  // Command ::= N+ := Expression+
//  //ok - verificado em 15/09/2005 às 15:15
//  public ActionSignature visitAssignmentCommand(AssignmentCommand term)
//  {    
//    assert term.getLHS() != null && term.getRHS() != null;
//    ZNameList LHS = term.getAssignmentPairs().getZLHS();
//    ZExprList RHS = term.getAssignmentPairs().getZRHS();
//    
//    if(LHS.size() != RHS.size()) {
//      Object [] params = {getCurrentActionName(), getCurrentProcessName()};
//      error(term, ErrorMessage.DIFF_NUM_ASSIG_COMMAND_ERROR, params);
//    }
//    else {
//      List<String> leftVars = new ArrayList<String>();
//      int i = 0;
//
//      for(RefName leftVarOld : vars) {
//        ZRefName leftVar = assertZRefName(leftVarOld);
//        Expr rigthExpr = exprs.get(i);
//        if(!leftVars.contains(leftVar.getWord())) {
//          leftVars.add(leftVar.getWord());
//          if(!isLovalVar(leftVar)) {
//            Object [] params = {assertZDeclName(currentAction()).getWord(), 
//                    assertZDeclName(currentProcess()).getWord(), leftVar.getWord()};
//            error(term, ErrorMessage.IS_NOT_LOCAL_VAR_NAME_IN_ASSIG_COMMAND, params);
//            break;
//          }
//          Type varType = typeEnv().getType(leftVar);
//          Type2 exprType = rigthExpr.accept(exprChecker());
//          if (unify(unwrapType(varType), unwrapType(exprType)) != SUCC) {
//            Object [] params = {assertZDeclName(currentAction()).getWord(), 
//                    assertZDeclName(currentProcess()).getWord(), varType, exprType, i+1};
//            error(term, ErrorMessage.ASSIG_COMMAND_ERROR, params);
//            break;
//          }   
//
//        } else {
//            Object [] params = {assertZDeclName(currentAction()).getWord(), 
//                    assertZDeclName(currentProcess()).getWord(), leftVar.getWord()};
//            error(term, ErrorMessage.DUPLICATE_VAR_NAME_IN_ASSIG_COMMAND, params);
//            break;
//        }
//        i++;
//      }
//    }
//        
//    ActionSignature actionSignature = factory().createActionSignature();
//    actionSignature.
//    addActionSignatureAnn(term, actionSignature);
//    return actionSignature;
//  }
//
//  // Command ::= N+ : [Predicate, Predicate]
//  // Command ::= [Predicate]
//  // Command ::= {Predicate}
//  //ok - verificado em 15/09/2005 às 15:17
//  public ActionSignature visitSpecStmtCommand(SpecStmtCommand term)
//  {      
//    ZRefNameList frameVars = term.getFrame() == null ? factory().createZRefNameList() : assertZRefNameList(term.getFrame());
//    Pred pre = term.getPre();
//    Pred post = term.getPost();
//    
//    List<String> frame = new ArrayList<String>();
//    
//    for(RefName frameVarOld : frameVars) {
//      ZRefName frameVar = assertZRefName(frameVarOld); 
//      if(!frame.contains(frameVar.getWord())) {
//        frame.add(frameVar.getWord());
//        if(!isLovalVar(frameVar)) {
//          Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), frameVar.getWord()};
//          error(term, ErrorMessage.IS_NOT_LOCAL_VAR_NAME_IN_SPEC_COMMAND, params);
//          break;
//        }
//      } else {
//          Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), frameVar.getWord()};
//          error(term, ErrorMessage.DUPLICATE_VAR_NAME_IN_FRAME_OF_SPEC_COMMAND, params);
//          break;
//      }
//    }
//    pre.accept(predChecker());
//    post.accept(predChecker());
//    
//    ActionSignature actionSignature = factory().createActionSignature();
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//
//  // Command ::= if GuardedActions fi
//  //ok - verificado em 15/09/2005 às 15:35
//  public ActionSignature visitIfGuardedCommand(IfGuardedCommand term)
//  {
//    ActionSignature actionSignature = factory().createActionSignature();
//    List<GuardedAction> gActions = term.getGuardedAction();
//    
//    for(GuardedAction gAction : gActions) {
//      Pred pred = gAction.getPred();
//      CircusAction action = gAction.getCircusAction();
//      pred.accept(predChecker());
//      ActionSignature sig = action.accept(actionChecker());
//      ActionSignature sigTemp = cloneActionSignature(sig);
//      actionSignature = joinActionSignature(actionSignature, sigTemp);
//    }
//    
//    addActionAnn(term, actionSignature);
//
//    return actionSignature;
//  }
//
//  // Command ::= var Declaration @ Action
//  //ok - vericado em 15/09/2005 às 16:04
//  public ActionSignature visitVarDeclCommand(VarDeclCommand term)
//  {
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    
//    ZDeclList decls = term.getZDeclList();
//    CircusAction action = term.getCircusAction();
//    
//    typeEnv().enterScope();
////    localCircTypeEnv().enterScope();
//  
//    List<Object> paramsError = new ArrayList<Object>();
//    paramsError.add(assertZDeclName(currentAction()).getWord());
//    paramsError.add(assertZDeclName(currentProcess()).getWord());
//    for(Decl d : decls){
//      if (!(d instanceof VarDecl))
//          throw new UnsupportedOperationException("Variable declaration command accepts only VarDecl!");
//      VarDecl decl = (VarDecl)d;
//      List<NameTypePair> pairs = decl.accept(declChecker());
//      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_PARAM_IN_PROCESS, paramsError);
//    }
//    // ADICIONAR AS VARIAÇÕES DAS VARIAVEIS DECLARADAS TAMBÉM
////    typeEnv().add(allPairs);
//    addVars(allPairs);
//    
//    ActionSignature actionSig = action.accept(actionChecker());
////    List<NameTypePair> usedChans = localCircTypeEnv().getUsedChans();
//    
////    localCircTypeEnv().exitScope();
//    typeEnv().exitScope();
//    
//    ActionSignature actionSignature = cloneActionSignature(actionSig);
//    actionSignature.setLocalVarsSignature(factory().createSignature(allPairs));
//
//    // adiciona os canais usados...
////    localCircTypeEnv().addUsedChans(usedChans);
//    
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//
//  /*
//  
//  // ParCommand ::= (QualifiedDeclaration @ Command)
//  // Falta testar!!
//  public ActionSignature visitParamCommand(ParamCommand term)
//  {
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    
//    List<QualifiedDecl> decls = term.getQualifiedDecl();
//    CircusCommand command = term.getCircusCommand();
//
//    typeEnv().enterScope();
//    
//    List<Object> paramsError = new ArrayList<Object>();
//    paramsError.add(assertZDeclName(currentAction()).getWord());
//    paramsError.add(assertZDeclName(currentProcess()).getWord());
//    for(QualifiedDecl qDecl : decls) {
//      List<NameTypePair> pairs = qDecl.accept(declChecker());
//      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_PARAM_IN_PARCOMMAND, paramsError);
//    }
//    addVars(allPairs);
//    
//    ActionSignature actionSig = command.accept(commandChecker());
//    
//    typeEnv().exitScope();
//    
//    ActionSignature actTemp = cloneActionSignature(actionSig);
//    actTemp.setLocalVarsSignature(factory().createSignature(allPairs));
//    
//    ActionSignature actionSignature = factory().createActionSignature();
//    actionSignature = joinActionSignature(actionSig, actTemp);    
//    
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//*/
}
