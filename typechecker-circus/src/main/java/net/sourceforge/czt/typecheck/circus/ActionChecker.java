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
import java.util.List;
import net.sourceforge.czt.circus.ast.Action1;
import net.sourceforge.czt.circus.ast.Action2;
import net.sourceforge.czt.circus.ast.ActionIte;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelAction;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelActionIte;
import net.sourceforge.czt.circus.ast.BasicAction;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusCommand;
import net.sourceforge.czt.circus.ast.GuardedAction;
import net.sourceforge.czt.circus.ast.HideAction;
import net.sourceforge.czt.circus.ast.InterleaveAction;
import net.sourceforge.czt.circus.ast.InterleaveActionIte;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ParallelAction;
import net.sourceforge.czt.circus.ast.ParallelActionIte;
import net.sourceforge.czt.circus.ast.ParamAction;
import net.sourceforge.czt.circus.ast.PrefixingAction;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.SubstitutionAction;
import net.sourceforge.czt.circus.visitor.Action1Visitor;
import net.sourceforge.czt.circus.visitor.Action2Visitor;
import net.sourceforge.czt.circus.visitor.ActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.BasicActionVisitor;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.CircusCommandVisitor;
import net.sourceforge.czt.circus.visitor.GuardedActionVisitor;
import net.sourceforge.czt.circus.visitor.HideActionVisitor;
import net.sourceforge.czt.circus.visitor.InterleaveActionIteVisitor;
import net.sourceforge.czt.circus.visitor.InterleaveActionVisitor;
import net.sourceforge.czt.circus.visitor.MuActionVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.ParamActionVisitor;
import net.sourceforge.czt.circus.visitor.PrefixingActionVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus.visitor.SubstitutionActionVisitor;
import net.sourceforge.czt.typecheck.circus.impl.ActionInfo;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZRenameList;


// TODO: CHECK: aSig.getFormalParams() could just be within getLocalVars(). add the qualification of the decl as an ann
/**
 * <p> bla bla bla </p>
 * <p>
 * Scopes in Circus have three layers. 
 * <dl>
 *  <dt>Global scope (S0)</dt>
 *    <dd>
 *      <p>
 *      Contains Z, channel, channel sets, and process paragraphs.
 *      It corresponds to the section scope of Z (i.e. name type pairs 
 *      within SectTypeEnv for a given section).
 *      </p>
 *    </dd>
 *  <dt>Process scope (S1)</dt>
 *    <dd>
 *      <p>
 *      Contains information local to a process: Z, name set, and 
 *      action paragraphs, as well as the process' formal parameters and 
 *      generic types.  These will form the ProcessSignature and type.
 *      </p>
 *    </dd>
 *  <dt>Action scope (S2)</dt>
 *    <dd>
 *      <p>
 *      Contains information local to the action of a process: variable 
 *      declarations, implicit variables from input prefixing, and 
 *      action formal parameters. Note that the first two will add four
 *      variables into scope (i.e., for var x: T we add x, x', x!, x?: T).
 *      These will form the ActionSignature and type. 
 *      </p>
 *      <p>
 *      As the declared variable types are important for other tools, we wrapp 
 *      such constructs with the special LetVarAction term, as done in the 
 *      model checker, and further detailed in Circus.xsd
 *      </p>
 *    </dd>
 * </dl>
 * </p>
 * @author Leo Freitas
 * @author Manuela
 */
public class ActionChecker
  extends Checker<ActionSignature> 
  implements 
             // DONE
             BasicActionVisitor<ActionSignature>,
               //SkipActionVisitor,                                      C.12.6
               //StopActionVisitor,                                      C.12.7
               //ChaosActionVisitor,                                     C.12.8
             SubstitutionActionVisitor<ActionSignature>,             //  C.12.9     
             PrefixingActionVisitor<ActionSignature>,                //  C.12.10
  
             // TODO
             Action1Visitor<ActionSignature>,
             Action2Visitor<ActionSignature>,
             SchExprActionVisitor<ActionSignature>,
             CallActionVisitor<ActionSignature>,
             //ActionDVisitor,
             MuActionVisitor<ActionSignature>,
             
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
  
  //ok - verificado em 15/09/2005 às 16:42
  public ActionSignature visitAction1(Action1 term)
  {
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());    
    addActionAnn(term, actionSignature);
    return actionSignature;
    
  }
  
  //ok - verificado em 15/09/2005 às 16:42
  public ActionSignature visitAction2(Action2 term)
  {
    ActionSignature actionSigL = term.getLeftAction().accept(actionChecker());
    ActionSignature actionSigR = term.getRightAction().accept(actionChecker());    
    ActionSignature result = joinActionSignature(actionSigL, actionSigR);    
    addActionAnn(term, result);
    return result;
  }

  /**
   * Returns an empty action signature. It covers Skip, Stop, and Chaos.
   *
   *@law C.12.?
   */  
  // Action ::= Schema-Exp  
  public ActionSignature visitSchExprAction(SchExprAction term)
  {
    ActionSignature actionSignature = factory().createActionSignature();

    Type typeExpr = term.getExpr().accept(exprChecker());

    SchemaType schType = (SchemaType)((PowerType)typeExpr).getType();
    Signature vars = schType.getSignature();
    actionSignature.setLocalVars(vars);

    addActionSignatureAnn(term, actionSignature);

    return actionSignature;
  }

  /**
   * Returns an empty action signature. It covers Skip, Stop, and Chaos.
   *
   *@law C.12.6, C.12.7, C.12.8
   */  
  // Action ::= Skip | Stop | Chaos
  public ActionSignature visitBasicAction(BasicAction term)
  {    
    assert isWithinActionParaScope() : "outside action para scope";
    
    // \Gamma \rhd Skip | Stop | Chaos : Action 
    ActionSignature actionSignature = factory().createActionSignature();
    addActionSignatureAnn(term, actionSignature);    
    return actionSignature;
  }  
  
  /**
   * This isometric resolution matrix is used to figure out where is the
   * problem for substitution names, if any. The line 0 represents the case
   * where NEW names are ok, whereas line 1 is when NEW names are invalid.
   * The same applies for columns and OLD names. This trick avoids too many
   * if/else statements.
   */
  private enum SubstResolution { Go, Old, New, Both };  
  private static final SubstResolution[][] SUBST_MATRIX = 
      {                    /* old name ok   old name bad */
        /* new name ok  */  { Go,           Old },  
        /* new name bad */  { New,          Both } 
      };
  
  /**
   *@law C.12.9
   */
  // Action ::= Action[N+ := N+]  // TODO!
  public ActionSignature visitSubstitutionAction(SubstitutionAction term)
  { 
    assert isWithinActionParaScope() : "outside action para scope";
           
    // the parser enforces              #ln1 = #ln2
    ZRenameList zrl = term.getZRenameList();    
    int i = 0;
    SubstResolution resolution;
    boolean hasError = false;
    for(NewOldPair nop : zrl) 
    {       
      // check both ln1 and ln2 are known local variables,   
      // (Into lnX \dom(\Gamma.localVars)) for X= {1,2}        
      ZName newName = nop.getZDeclName();
      ZName oldName = nop.getZRefName();
      
      // retrieve the resolution from the valid subsitution list
      // TODO: DECISION: do not stop in case of error, but report it; or stop it?
      resolution = SUBST_MATRIX[(isLocalVar(newName) ? 1 : 0)]
                               [(isLocalVar(oldName) ? 1 : 0)];        
      if (resolution.equals(SubstResolution.Go))
      {
        assert false : "TODO";
        /*
        Type2 expectedU = unwrapType(typeEnv().getType(oldName));
        Type2 foundU = unwrapType(typeEnv().getType(newName));
        // TODO: CHECK: should we add this to the unification environment
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
        // TODO: CHECK: could this result be partial?
        else if (unify(foundU, expectedU) != SUCC) {
          Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), 
                              assertZDeclName(actionSignature.getActionName()).getWord(), expectedU, foundU, i+1};
          error(term, ErrorMessage.ACTION_RENAME_NOT_UNIFY, params);
          break;
        }
         **/
      } 
      else
      {
         String name = "";
         switch (resolution) 
         {
           case New: name = newName.toString();  break;
           case Old: name = oldName.toString();  break;
           case Both: name = newName.toString() + " and " + 
                             oldName.toString(); break;
         }           
         Object [] params = { resolution, name, (i+1), getCurrentActionName(), getCurrentProcessName() };
         error(term, ErrorMessage.NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION, params);                     
      }        
      i++;        
    }
    
    // check the action to substitute,  \Gamma \rhd a: Action
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());
    addActionSignatureAnn(term, actionSignature);        
    return actionSignature;    
  }
  
  
  /**
   * Returns an action signature containing the list  . It covers Skip, Stop, and Chaos.
   *@law C.12.10
   */
  // Action ::= Communication -> Action  
  public ActionSignature visitPrefixingAction(PrefixingAction term)
  {
    // enter the scope for input fields
    typeEnv().enterScope();
    
    // typecheck the communication part returning a list of name type pairs
    // it returns the input variables that need to be declared.
    // * calculate (VarsC c \Gamma)
    List<NameTypePair> comSig = term.getCommunication().accept(commChecker());    
    List<NameTypePair>inputVars = commChecker().filterInputs(comSig); 
    
    // Adds input variables into S1. The oplus at the signature level is implemented down below.
    // * create \Gamma' = (\Gamma \oplus (VarsC c \Gamma)) 
    // 
    // NOTE: variables should be added locally at the input field 
    //addLocalVars(inputVars);
    
    // type check given action in scope enriched with input variables
    // * checks \Gamma' \rhd a : Action
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());
    
    actionSignature.getLocalVars()
    
    // should contain the communication expressions!
    actionSignature.getUsedChannels().
        
    // override the signature of variables: outermost variables have precedence
    // so, the example above c?x -> d?x -> A(x) is viewed as
    // ex: term = c?x -> term1
    //     term1= d?x -> term2(x)
    //
    // sigTerm2 = sig(Term2)
    // sigTerm1 = sigTerm2 \oplus sigTerm1
    // sigTerm  = sigTerm1 \oplus sigTerm
    Signature actSigLocals = actionSignature.getLocalVars();
    
    // override the signatures resolving any Variable types involved
    // (i.e. those still in need of generic type inference)
    overrideSignature(commSig, actSigLocals); // actSigLocals \oplus comSig
    
    // close input variables scope after analysing the entailing action
    typeEnv().exitScope();
 
    addActionSignatureAnn(term, actionSignature);    
    return actionSignature;
  }
  
  /**
   *@law C.12.11
   */
  // Action ::= Predicate & Action  
  public ActionSignature visitGuardedAction(GuardedAction term)
  {
    term.getPred().accept(predChecker());
    ActionSignature signature = term.getCircusAction().accept(actionChecker());
    addActionAnn(term, signature);
    
    return signature;
  }

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
