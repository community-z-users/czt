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

import java.util.ArrayList;
import net.sourceforge.czt.circustools.ast.ActionType;
import net.sourceforge.czt.circustools.ast.ChanSetType;
import net.sourceforge.czt.circustools.ast.NameSetType;
import net.sourceforge.czt.typecheck.circus.impl.ActionInfo;
import static net.sourceforge.czt.z.util.ZUtils.*;
import static net.sourceforge.czt.typecheck.circus.util.GlobalDefs.*;

import java.util.List;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.*;
import net.sourceforge.czt.circustools.ast.ActionSignature;
import net.sourceforge.czt.z.util.ZString;



/**
 *
 * @author Leo Freitas
 * @author Manuela
 */
public class ActionChecker
  extends Checker<ActionSignature> 
  implements //CircusActionVisitor,
             Action1Visitor<ActionSignature>,
             Action2Visitor<ActionSignature>,
             SchExprActionVisitor<ActionSignature>,
             BasicActionVisitor<ActionSignature>,
             CallActionVisitor<ActionSignature>,
             //ChaosActionVisitor,
             //SkipActionVisitor,
             //StopActionVisitor,
             //ActionDVisitor,
             MuActionVisitor<ActionSignature>,
             PrefixingActionVisitor<ActionSignature>,
             SubstitutionActionVisitor<ActionSignature>,
             GuardedActionVisitor<ActionSignature>,
             HideActionVisitor<ActionSignature>,
             ActionIteVisitor<ActionSignature>,
             ParamActionVisitor<ActionSignature>,
             //ParActionIteVisitor,
             //ExtChoiceActionIteVisitor,
             //IntChoiceActionIteVisitor,
             //SeqActionIteVisitor,
             AlphabetisedParallelActionIteVisitor<ActionSignature>,
             InterleaveActionIteVisitor<ActionSignature>,
             ParallelActionIteVisitor<ActionSignature>,
             //ExtChoiceActionVisitor,
             //IntChoiceActionVisitor,
             //SeqActionVisitor,
             //ParActionVisitor,
             InterleaveActionVisitor<ActionSignature>,
             ParallelActionVisitor<ActionSignature>,
             AlphabetisedParallelActionVisitor<ActionSignature>,
             CircusCommandVisitor<ActionSignature>
{
  
  //a Z decl checker
  protected net.sourceforge.czt.typecheck.z.DeclChecker zDeclChecker_;

  /** Creates a new instance of ActionChecker */
  public ActionChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zDeclChecker_ =
      new net.sourceforge.czt.typecheck.z.DeclChecker(typeChecker);
  }
  
//  public Object visitCircusAction(CircusAction term)
//  {
//    return term.accept(actionChecker());
//  }

  //ok - verificado em 15/09/2005 às 16:42
  public ActionSignature visitAction1(Action1 term)
  {
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());
    // TODO: Check: added for consistency
    addActionAnn(term, actionSignature);
    return actionSignature;
    
  }
  
  //ok - verificado em 15/09/2005 às 16:42
  public ActionSignature visitAction2(Action2 term)
  {
    ActionSignature actionSigL = term.getLeftAction().accept(actionChecker());
    ActionSignature actionSigR = term.getRightAction().accept(actionChecker());    
    ActionSignature result = joinActionSignature(actionSigL, actionSigR);
    // TODO: Check: added for consistency
    addActionAnn(term, result);
    return result;
  }

  // Action ::= Schema-Exp
  //ok - verificado em 15/09/2005 às 16:50
  public ActionSignature visitSchExprAction(SchExprAction term)
  {
    ActionSignature actionSignature = factory().createActionSignature();

    Type2 typeExpr = term.getExpr().accept(exprChecker());

    SchemaType schType = (SchemaType)((PowerType)typeExpr).getType();
    Signature vars = schType.getSignature();
    actionSignature.setLocalVarsSignature(vars);

    addActionAnn(term, actionSignature);

    return actionSignature;
  }

  //ok - verificado em 15/09/2005 às 16:52
  public ActionSignature visitBasicAction(BasicAction term)
  {
    ActionSignature actionSignature = factory().createActionSignature();
    addActionAnn(term, actionSignature);
    return actionSignature;
  }

  // Action ::= Chaos
  //ok - verificado em 15/09/2005 às 16:52
//  public Object visitChaosAction(ChaosAction term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitBasicAction(term);
//
//    addActionAnn(term, actionSignature);
//
//    return actionSignature;
//  }

  // Action ::= Skip
  //ok - verificado em 15/09/2005 às 16:52
//  public Object visitSkipAction(SkipAction term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitBasicAction(term);
//
//    addActionAnn(term, actionSignature);
//
//    return actionSignature;
//  }

  // Action ::= Stop
  //ok - verificado em 15/09/2005 às 16:52
//  public Object visitStopAction(StopAction term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitBasicAction(term);
//
//    addActionAnn(term, actionSignature);
//
//    return actionSignature;
//  }

  // Action ::= N
  // Action ::= N(Expression+)
  // Action ::= (Declaration @ Action)(Expression+)
  // Action ::= (\mu N @ ParAction)(Expression+)
  //ok - verificado em 15/09/2005 às 17:02
  public ActionSignature visitCallAction(CallAction term)
  {
    ActionSignature actionSignature = factory().createActionSignature();
    ZRefName actionRef = assertZRefName(term.getRefName());
    ZDeclName actionDecl = factory().createZDeclName(actionRef);
    
    if(assertZDeclName(actionDecl).getWord().startsWith("$$implicitAction_")) {
      // pegar da lista de ações implícitos, fazer a verificação e incluir no
      // TypeEnv!!
      List<ActionPara> implicitActions = (List<ActionPara>)localCircTypeEnv().getOnTheFlyActions();
      for(ActionPara implicitAction : implicitActions) {
        if(compareDeclName(actionDecl, implicitAction.getDeclName(), true)) {
          Signature implicitActionSig = implicitAction.accept(paraChecker());
        }
      }
    }
    
    // verifica se é uma chamada a uma ação mu
    if(isMuAction(actionDecl)) {
      if(!(term.getZExprList().isEmpty())) {
        Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), assertZDeclName(actionDecl).getWord()};
        error(term, ErrorMessage.MU_ACTION_CALL_ERROR, params);
      }
    }// caso não seja uma chamada a uma ação mu
    else {
      Type typeRefName = typeEnv().getType(actionRef);

      if(!(typeRefName instanceof UnknownType)) {
        if(!localCircTypeEnv().isAction(actionDecl)) {
          Object [] params = {assertZDeclName(actionDecl).getWord()};
          error(term, ErrorMessage.IS_NOT_ACTION_NAME, params);
        } 
        else {
          if(typeRefName instanceof ActionType) {
            ActionType actionType = (ActionType)typeRefName;
            actionSignature = actionType.getActionSignature();
          }
          // a ação é um schExpr
          else {
            SchemaType schType = (SchemaType)((PowerType)typeRefName).getType();
            Signature vars = schType.getSignature();
            actionSignature.setActionName(actionDecl);
            actionSignature.setLocalVarsSignature(vars);
          }
          
          List<NameTypePair> params = null;
          if(actionSignature.getParams() != null) {
            params = actionSignature.getParams().getNameTypePair();
          }          
          // chama um método auxiliar que irá verificar se a chamada está correta
          checkCallAction(term, params);
        }
      } 
      else {
        if(!(actionDecl.equals(currentAction()))){
//          Object [] params = {actionDecl.getWord()};
//          error(term, ErrorMessage.IS_NOT_ACTION_NAME, params);
          //add this reference for post checking
          if (!containsObject(paraErrors(), term)) {
            paraErrors().add(term);
            addAction4PostCheck(currentAction());
          }
        }
        else {
          // tratamento especial para o caso de chamada recursiva
          List<NameTypePair> params = localCircTypeEnv().getActionInfo(actionDecl).getParams();
          // chama um método auxiliar que irá verificar se a chamada está correta
          checkCallAction(term, params);
        }
      }
    }
    
    addActionAnn(term, actionSignature);
    
    return actionSignature;
  }
  
  //ok - verificado em 15/09/2005 às 17:02
//  public Object visitActionD(ActionD term)
//  { // Loop!      
//    return term.accept(actionChecker());
//  }
  
  // Action ::= \mu N @ Action
  //ok - verificado em 15/09/2005 às 17:03
  public ActionSignature visitMuAction(MuAction term)
  {
    DeclName name = term.getDeclName();
    CircusAction action = term.getCircusAction();
    
    addMuAction(name);
    ActionSignature signature = action.accept(actionChecker());
    removeMuAction(name);
    
    addActionAnn(term, signature);
    
    return signature;
  }
  
  // Action ::= Communication -> Action
  //ok -  verificado em 15/09/2005 às 17:05
  public ActionSignature visitPrefixingAction(PrefixingAction term)
  {
    CircusAction action = term.getCircusAction();
    
    List<NameTypePair> inputVars = term.getCommunication().accept(communicChecker());

    typeEnv().enterScope();

    addVars(inputVars);

    ActionSignature actionSignature = action.accept(actionChecker());

    typeEnv().exitScope();
 
    addActionAnn(term, actionSignature);    
    return actionSignature;
  }

  // Action ::= Action[N+ := N+]
  //ok - verificado em 15/09/2005 às 17:06
  public ActionSignature visitSubstitutionAction(SubstitutionAction term)
  {
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());
    ZRenameList zrl = term.getZRenameList();    
    int i = 0;
    for(NewOldPair nop : zrl) {        
        ZRefName newName = factory().createZRefName(nop.getZDeclName());
        ZRefName oldName = nop.getZRefName();
        if(!isLovalVar(oldName)) {
          Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), oldName.getWord()};
          error(term, ErrorMessage.IS_NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION, params);
          break;
        } 
        else if (!isLovalVar(newName)) {
          Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), newName.getWord()};
          error(term, ErrorMessage.IS_NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION, params);
          break;
        }
        else {
          Type2 expectedU = unwrapType(typeEnv().getType(oldName));
          Type2 foundU = unwrapType(typeEnv().getType(newName));
          if(foundU instanceof UnknownType) {
            Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), 
                                assertZDeclName(actionSignature.getActionName()).getWord(), newName.getWord()};
            error(term, ErrorMessage.RENAME_ACTION_UNDECLARED_VAR, params);
          } 
          else if(expectedU instanceof UnknownType) {
            Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), 
                                assertZDeclName(actionSignature.getActionName()).getWord(), oldName.getWord()};
            error(term, ErrorMessage.RENAME_ACTION_UNDECLARED_VAR, params);
          }
          else if (unify(foundU, expectedU) != SUCC) {
            Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), 
                                assertZDeclName(actionSignature.getActionName()).getWord(), expectedU, foundU, i+1};
            error(term, ErrorMessage.ACTION_RENAME_NOT_UNIFY, params);
            break;
          }   
          i++;
        }
    }
    addActionAnn(term, actionSignature);
    return actionSignature;
    /*
    ActionSignature actionSignature = (ActionSignature)term.getCircusAction().accept(actionChecker());
    
    List<RefName> oldNames = (List<RefName>)term.getOldNames();
    List<RefName> newNames = (List<RefName>)term.getNewNames();
    
    if(oldNames.size() == newNames.size()) {
      int i = 0;
      for(RefName oldName : (List<RefName>)oldNames) {
        RefName newName = newNames.get(0);

        if(!isLovalVar(oldName)) {
          Object [] params = {currentAction().getWord(), currentProcess().getWord(), oldName.getWord()};
          error(term, ErrorMessage.IS_NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION, params);
          break;
        } 
        else if (!isLovalVar(newName)) {
          Object [] params = {currentAction().getWord(), currentProcess().getWord(), newName.getWord()};
          error(term, ErrorMessage.IS_NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION, params);
          break;
        }
        else {
          Type2 expectedU = unwrapType(typeEnv().getType(oldName));
          Type2 foundU = unwrapType(typeEnv().getType(newName));
          if(foundU instanceof UnknownType) {
            Object [] params = {currentAction().getWord(), currentProcess().getWord(), 
                                actionSignature.getActionName().getWord(), newName.getWord()};
            error(term, ErrorMessage.RENAME_ACTION_UNDECLARED_VAR, params);
          } 
          else if(expectedU instanceof UnknownType) {
            Object [] params = {currentAction().getWord(), currentProcess().getWord(), 
                                actionSignature.getActionName().getWord(), oldName.getWord()};
            error(term, ErrorMessage.RENAME_ACTION_UNDECLARED_VAR, params);
          }
          else if (unify(foundU, expectedU) != SUCC) {
            Object [] params = {currentAction().getWord(), currentProcess().getWord(), 
                                actionSignature.getActionName().getWord(), expectedU, foundU, i+1};
            error(term, ErrorMessage.ACTION_RENAME_NOT_UNIFY, params);
            break;
          }   
          i++;
        }
      }
    } else {
      Object [] params = {currentAction().getWord(), currentProcess().getWord(), 
                          actionSignature.getActionName().getWord(), oldNames.size(), newNames.size()};
      error(term, ErrorMessage.ACTION_RENAME_DIFF_NUMBER_VARS, params);
    }
    
    addActionAnn(term, actionSignature);
    return actionSignature;
     **/
  }
  
  // Action ::= Predicate & Action
  //ok - verificado em 15/09/2005 às 17:08
  public ActionSignature visitGuardedAction(GuardedAction term)
  {
    term.getPred().accept(predChecker());
    ActionSignature signature = term.getCircusAction().accept(actionChecker());
    addActionAnn(term, signature);
    
    return signature;
  }
  
  // Action ::= Action \ CSExpression
  //ok - verificado em 15/09/2005 às 17:09
  public ActionSignature visitHideAction(HideAction term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //
    
    ActionSignature signature = term.getCircusAction().accept(actionChecker());
    addActionAnn(term,  signature);
    
    return signature;
  }
  
  //ok - verificado em 15/09/2005 às 17:47
  public ActionSignature visitActionIte(ActionIte term)
  {  
    ZDeclList decs = term.getZDeclList();
    CircusAction action = term.getCircusAction();

    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
    List<Object> paramsError = new ArrayList<Object>();
    paramsError.add(assertZDeclName(currentAction()).getWord());
    paramsError.add(assertZDeclName(currentProcess()).getWord());

    for(Decl d : decs) {
      if (!(d instanceof VarDecl))
          throw new UnsupportedOperationException("Iterated actions accept only VarDecl!");
      VarDecl dec = (VarDecl)d;
      boolean declOK = false;
      if(dec.getExpr() instanceof SetExpr) {
        declOK = true;
      }
      else if(dec.getExpr() instanceof ApplExpr) {
        ApplExpr applExpr = (ApplExpr)dec.getExpr();
        if(applExpr.getLeftExpr() instanceof RefExpr) {
          if(((RefExpr)applExpr.getLeftExpr()).getZRefName().getWord().equals(ZString.ARG_TOK + ".." + ZString.ARG_TOK)) {
            declOK = true;
          }
        }
      }
      List<NameTypePair> pairs = (List<NameTypePair>)dec.accept(declChecker());
      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_VAR_IN_ACTION_ITE, paramsError);
      if(!declOK) {
        Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord()};
        error(term, ErrorMessage.INFINITY_VALUES_IN_ACTION_ITE, params);
        break;
      }
    }
    typeEnv().enterScope();

    typeEnv().add(allPairs);
    ActionSignature actionSig = action.accept(actionChecker());
    ActionSignature actionSignature = cloneActionSignature(actionSig);
    Signature sig = factory().createSignature(allPairs);
    actionSignature.setLocalVarsSignature(sig);
    
    typeEnv().exitScope();
    // TODO: added for consistency.
    addActionAnn(term,  actionSignature);

    return actionSignature;
  }

  // Action ::= Declaration @ Action
  //ok - verificado em 15/09/2005 às 18:12
  public ActionSignature visitParamAction(ParamAction term)
  {
    ZDeclList decls = term.getZDeclList();
    CircusAction action = term.getCircusAction();

    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
    List<Object> paramsError = new ArrayList<Object>();
    paramsError.add(assertZDeclName(currentAction()).getWord());
    paramsError.add(assertZDeclName(currentProcess()).getWord());

    for(Decl d : decls) {
      if (!(d instanceof VarDecl))
        throw new UnsupportedOperationException("Parameterised actions accept only VarDecl!");
      VarDecl decl = (VarDecl)d;
      List<NameTypePair> pairs = decl.accept(declChecker());
      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_PARAM_IN_ACTION, paramsError);
    }
    
    // atualiza informações sobre a ação
    ActionInfo actionInfo = localCircTypeEnv().getActionInfo(currentAction());
    actionInfo.setIsParam(true);
    actionInfo.setParams(allPairs);

    typeEnv().enterScope();
    
    typeEnv().add(allPairs);    
    ActionSignature actionSig = action.accept(actionChecker());
    ActionSignature actionSignature = cloneActionSignature(actionSig);
    Signature varsSig = factory().createSignature(allPairs);
    actionSignature.setParams(varsSig);
    typeEnv().exitScope();
    
    addActionAnn(term, actionSignature);
    
    return actionSignature;
  }
  
  // existe ?!?
  //ok - verificado em 15/09/2005 às 17:50
//  public Object visitParActionIte(ParActionIte term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
  
  // Action ::= \Extchoice Declaration @ Action
  //ok - verificado em 15/09/2005 às 17:50
//  public Object visitExtChoiceActionIte(ExtChoiceActionIte term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//  
//  // Action ::= \Intchoice Declaration @ Action
//  //ok - verificado em 15/09/2005 às 17:50
//  public Object visitIntChoiceActionIte(IntChoiceActionIte term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//
//  // Action ::= \Semi Declaration @ Action
//  //ok - verificado em 15/09/2005 às 17:50
//  public Object visitSeqActionIte(SeqActionIte term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }

  // Action ::= \Parallel Declaration @ |[NSExpression | CSExpression]| Action
  // Action ::= \Parallel Declaration @ |[CSExpression]| Action
  //ok - verificado em 15/09/2005 às 17:52
  public ActionSignature visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //

    NameSetType typeNS = (NameSetType)term.getNameSet().accept(exprChecker());

    ActionSignature actionSignature = visitActionIte(term);
    //addActionAnn(term, actionSignature);
    
    return actionSignature;
  }

  // Action ::= \Interleave Declaration @ Action
  // Action ::= \Interleave Declaration @ ||[NSExpression]|| Action
  //ok - verificado em 15/09/2005 às 17:53
  public ActionSignature visitInterleaveActionIte(InterleaveActionIte term)
  {
    NameSetType typeNS = (NameSetType)term.getNameSet().accept(exprChecker());
    
    ActionSignature actionSignature = visitActionIte(term);
    //addActionAnn(term, actionSignature);
    
    return actionSignature;
  }

  // Action ::= |[CSExpression]| Declaration @ |[NSExpression]| Action
  // Action ::= |[CSExpression]| Declaration @ Action
  //ok - verificado em 15/09/2005 às 17:52
  public ActionSignature visitParallelActionIte(ParallelActionIte term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //

    NameSetType typeNS = (NameSetType)term.getNameSet().accept(exprChecker());

    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
    addActionAnn(term, actionSignature);
    
    return actionSignature;
  }
  
  // Action ::= Action \extchoice Action
  //ok - verificado em 15/09/2005 às 18:00
//  public Object visitExtChoiceAction(ExtChoiceAction term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitAction2(term);
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//
//  // Action ::= Action \intchoice Action
//  //ok - verificado em 15/09/2005 às 18:01
//  public Object visitIntChoiceAction(IntChoiceAction term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitAction2(term);
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//
//  // Action ::= Action ; Action
//  //ok - verificado em 15/09/2005 às 18:01
//  public Object visitSeqAction(SeqAction term)
//  {
//    ActionSignature actionSignature = (ActionSignature)visitAction2(term);
//    addActionAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//  
//  //existe?!?
//  //ok - verificado em 15/09/2005 às 18:02
//  public Object visitParAction(ParAction term)
//  {
//    return visitAction2(term);
//  }

  // Action ::= Action \interleave Action
  // Action ::= Action ||[NSExpression | NSExpressio]|| Action
  //ok - verificado em 15/09/2005 às 18:04
  public ActionSignature visitInterleaveAction(InterleaveAction term)
  {
    NameSetType typeNSL = (NameSetType)term.getLeftNameSet().accept(exprChecker());
    NameSetType typeNSR = (NameSetType)term.getRightNameSet().accept(exprChecker());

    ActionSignature actionSignature = visitAction2(term);
    //addActionAnn(term, actionSignature);    
    return actionSignature;
  }

  // Action ::= Action |[CSExpression]| Action
  // Action ::= Action |[NSExpression | CSExpression | NSExpression]| Action
  //ok - verificado em 15/09/2005 às 18:07
  public ActionSignature visitParallelAction(ParallelAction term)
  {
    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
    //
    
    // TODO: Check why you are doing it twice!?
    //NameSetType typeNSL = (NameSetType)term.getLeftNameSet().accept(exprChecker());
    //NameSetType typeNSR = (NameSetType)term.getRightNameSet().accept(exprChecker());

    term.getLeftNameSet().accept(exprChecker());
    term.getRightNameSet().accept(exprChecker());
    ActionSignature actionSignature = visitAction2(term);
    //addActionAnn(term, actionSignature);
    
    return actionSignature;
  }

  // Action ::= Action |[CSExpression || CSExpression]| Action
  // Action ::= Action |[NSExpression | CSExpression || CSExpression | NSExpression]| Action
  //ok - verificado em 15/09/2005 às 18:
  public ActionSignature visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
  {
    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
    ChanSetType typeCSL = (ChanSetType)term.getLeftAlpha().accept(exprChecker());
    ChanSetType typeCSR = (ChanSetType)term.getRightAlpha().accept(exprChecker());
    allPairs.addAll(typeCSL.getChannels().getNameTypePair());
    allPairs.addAll(typeCSR.getChannels().getNameTypePair());
    // adicionando os canais usados...
    localCircTypeEnv().addUsedChans(allPairs);
    //
    
   // NameSetType typeNSL = (NameSetType)term.getLeftNameSet().accept(exprChecker());
   // NameSetType typeNSR = (NameSetType)term.getRightNameSet().accept(exprChecker());

    term.getLeftNameSet().accept(exprChecker());
    term.getRightNameSet().accept(exprChecker());
    ActionSignature actionSignature = visitAction2(term);
    //addActionAnn(term, actionSignature);
    
    return actionSignature;
  }

  // Action ::= ParamCommand
  //ok - verificado em 15/09/2005 às 18:10
  public ActionSignature visitCircusCommand(CircusCommand term)
  {
    return term.accept(commandChecker());
  }

  // Funções auxiliares
  
  private boolean checkCallActionParamTypes(DeclName actionName, List<NameTypePair> decs, List<Type2> types){
    boolean result = true;
    int i = 0;
    if(decs.size() == types.size()) {
      for(NameTypePair pair : decs) {
        Type2 expectedU = unwrapType(pair.getType());
        Type2 foundU = unwrapType(types.get(i));
        if(foundU instanceof UnknownType) {
          Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), assertZDeclName(actionName).getWord(), i+1};
          error(actionName, ErrorMessage.PARAM_ACTION_CALL_UNDECLARED_VAR, params);
          result = false;
          break;
        }
        if(unify(foundU, expectedU) != SUCC) {
          Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), assertZDeclName(actionName).getWord(), expectedU, foundU, i+1};
          error(actionName, ErrorMessage.PARAM_ACTION_CALL_NOT_UNIFY, params);
          result = false;
          break;
        }   
        i++;
      }
    } else {
      Object [] params = {decs.size(), types.size(), assertZDeclName(actionName).getWord()};
      error(actionName, ErrorMessage.ACTION_CALL_DIFF_NUMBER_EXPRS, params);
      result = false;
    }
    
    return result;
  }

  private void checkCallAction(CallAction term, List<NameTypePair> params) {
    
    ZDeclName actionDecl = factory().createZDeclName(assertZRefName(term.getRefName()));
    
    // TODO: Check this comment.
    // CallType.Param
    if (!term.getZExprList().isEmpty()) {
        if(!localCircTypeEnv().isParamAction(actionDecl)){
          Object [] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), actionDecl.getWord()};
          error(term, ErrorMessage.IS_NOT_PARAM_ACTION_IN_ACTION_CALL, paramsError);
        }
        else {
          List<Type2> typeExprs = new ArrayList<Type2>();
          ZExprList exprs = term.getZExprList();
          for(Expr expr : exprs) {
            Type2 type = expr.accept(exprChecker());
            typeExprs.add(type);
          }
          // TODO: For what purpose the returned boolean value is useful?
          checkCallActionParamTypes(actionDecl, params, typeExprs);
        }
    } 
    // CallType.Normal
    else {
       if(localCircTypeEnv().isParamAction(actionDecl)) {
          Object [] paramsError = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), actionDecl.getWord()};
          error(term, ErrorMessage.PARAM_ACTION_CALL_WITHOUT_EXPRS, paramsError);
        } 
    }    
  }  
}
