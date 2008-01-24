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
import net.sourceforge.czt.circus.ast.Action1;
import net.sourceforge.czt.circus.ast.Action2;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.BasicAction;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.CircusCommand;
import net.sourceforge.czt.circus.ast.GuardedAction;
import net.sourceforge.czt.circus.ast.HideAction;
import net.sourceforge.czt.circus.ast.InterleaveAction;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ParallelAction;
import net.sourceforge.czt.circus.ast.PrefixingAction;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.SubstitutionAction;
import net.sourceforge.czt.circus.visitor.Action2Visitor;
import net.sourceforge.czt.circus.visitor.BasicActionVisitor;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.CircusCommandVisitor;
import net.sourceforge.czt.circus.visitor.GuardedActionVisitor;
import net.sourceforge.czt.circus.visitor.HideActionVisitor;
import net.sourceforge.czt.circus.visitor.InterleaveActionVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.PrefixingActionVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus.visitor.SubstitutionActionVisitor;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.impl.VariableSignature;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.z.ast.GenericType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZRenameList;


// TODO: CHECK: aSig.getFormalParams() could just be within getLocalVars(). add the qualification of the decl as an ann
import net.sourceforge.czt.z.util.ZUtils;
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
             SchExprActionVisitor<ActionSignature>,                  //  C.12.3
             CallActionVisitor<ActionSignature>,                     //  C.12.4, C.12.19
             CircusCommandVisitor<ActionSignature>,                  //  C.12.5
             BasicActionVisitor<ActionSignature>,
               //SkipActionVisitor,                                      C.12.6
               //StopActionVisitor,                                      C.12.7
               //ChaosActionVisitor,                                     C.12.8
             SubstitutionActionVisitor<ActionSignature>,             //  C.12.9     
             PrefixingActionVisitor<ActionSignature>,                //  C.12.10
             GuardedActionVisitor<ActionSignature>,                  //  C.12.11
             Action2Visitor<ActionSignature>,                        
               //SeqActionIteVisitor,                                    C.12.12
               //ExtChoiceActionIteVisitor,                              C.12.13
               //IntChoiceActionIteVisitor,                              C.12.14
               //ParActionIteVisitor (i.e. interleave, no name set),     C.12.15  
             InterleaveActionVisitor<ActionSignature>,               //  C.12.16
             ParallelActionVisitor<ActionSignature>,                 //  C.12.17             
             HideActionVisitor<ActionSignature>//,                     //  C.12.18
        
//             // TODO
//             //Action1Visitor<ActionSignature>,                          
//             
//             
//             //ActionDVisitor,
//             MuActionVisitor<ActionSignature>,
//             
//             
//             
//             ActionIteVisitor<ActionSignature>,
//             ParamActionVisitor<ActionSignature>,
//             
//             
//             AlphabetisedParallelActionIteVisitor<ActionSignature>,
//             
//             ParallelActionIteVisitor<ActionSignature>,
//             //ExtChoiceActionVisitor,
//             //IntChoiceActionVisitor,
//             //SeqActionVisitor,
//             //ParActionVisitor,
//             InterleaveActionIteVisitor<ActionSignature>,
//             
//             AlphabetisedParallelActionVisitor<ActionSignature>,
//             
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

  /**
   * Returns an empty action signature. It covers Skip, Stop, and Chaos.
   *
   *@law C.12.3
   */    
  @Override
  public ActionSignature visitSchExprAction(SchExprAction term)
  {
    // Action ::= Schema-Exp    
    checkActionParaScope(term, null);
    
    ActionSignature actionSignature = factory().createEmptyActionSignature();
    
    // type check the schema expressions
    // TODO: CHECK: should use processParaChecker?
    Type type = term.getExpr().accept(exprChecker());    
    
    SchemaType schType = referenceToSchema(type);
    if (schType != null)
    {
      Signature signature = schType.getSignature();
      
      // resolve any variable type
      if (!(signature instanceof VariableSignature)) {
        Signature sig = createNewIds(signature);
        SchemaType newSchemaType = factory().createSchemaType(sig);
        type = factory().createPowerType(newSchemaType);
        signature = sig;
      }            
      
      // make sure all names are in (process) scope
      for(NameTypePair pair : signature.getNameTypePair())
      {
        Type2 expected = GlobalDefs.unwrapType(getType(pair.getName()));
        
        if (expected instanceof UnknownType)
        {          
          Object[] params = { getCurrentProcessName(), getCurrentActionName(), term };
          error(term, ErrorMessage.SCHEXPR_ACTION_UNKNOWN_VAR, params);
        
        }
        else
        {
          Type2 found = GlobalDefs.unwrapType(pair.getType());        
          UResult unified = unify(found, expected);        
          if (unified.equals(UResult.FAIL))
          {
            Object[] params = { getCurrentProcessName(), getCurrentActionName(), 
              term, expected, found };
            error(term, ErrorMessage.SCHEXPR_ACTION_FAIL_UNIFY, params);
          }
        }        
      }      
    }
    // not a schema expression in a schema expression action
    else
    {
      Object[] params = { getCurrentProcessName(), getCurrentActionName(), term, type };
      error(term, ErrorMessage.NON_SCHEXPR_IN_SCHEXPR_ACTION, params);
    }
    
    addActionSignatureAnn(term, actionSignature);

    return actionSignature;
  }
  
  /**
   * This visiting method represents all forms of action call. They are:
   * simple calls A, parameterised calls A(el), or on-the-fly calls, 
   * which can be either simple or parameterised. The parser is responsible
   * for making on-the-fly actions implicitly declared (with a special internal
   * name, see {@link net.sourceforge.czt.circus.ast.util.CircusString}). The 
   * action declaration for the on-the-fly action also has a OnTheFlyDefAnn.
   * Tools building actions on-the-fly dynamically MUST follow the protocol.
   *
   *@law C.12.4, C.12.19
   */    
  //ok - verificado em 15/09/2005 às 17:02
  public ActionSignature visitCallAction(CallAction term)
  {
    // NOTE: Most of this code follows the pattern from z.ExprChecker.visitRefExpr.
    
    // Action ::= N
    // Action ::= N(Expression+)
    // Action ::= (Declaration @ Action)(Expression+)
    // Action ::= (\mu N @ ParAction)(Expression+)
    
    // retrieve the type of this name.
    Name call = term.getName();
    
    checkActionParaScope(term, call);
    
    Type type = getType(call);
        
    boolean addedPostChecking = false;
    //add this reference for post checking --- this is CZT's approach
    if (!GlobalDefs.containsObject(paraErrors(), term)) {
      // TODO: double check on this as manuela's solution is different from CZT's'
      //       in hers, this is only added within a particular case when the 
      //       action type is unknown and the current action name is different from 
      //       the one being called.
      if (!ZUtils.namesEqual(getCurrentActionName(), call))
      {
        paraErrors().add(term);      
        //addAction4PostCheck(getCurrentActionName());
        addedPostChecking = true; // see this flag below.
      }
    }
    
    //if this is undeclared, create an unknown type with this CallAction
    //i.e., getType(call) may add a UndeclaredAdd to call
    Object undecAnn = call.getAnn(UndeclaredAnn.class);
    
    //if we are using name IDs, then read the type off the name if it
    //is not in the type environment    
    // TODO: CHECK: ask Tim, this is a known name then?
    if (undecAnn != null && sectTypeEnv().getUseNameIds()) {      
      type = GlobalDefs.getTypeFromAnns(term);
      if (!(type instanceof UnknownType)) {
        GlobalDefs.removeAnn(call, UndeclaredAnn.class);
        undecAnn = null;
      }
    }
    
    // if name is unknown, add the call to its list of associated names.
    if (undecAnn != null) 
    {
      assert type instanceof UnknownType;
      UnknownType uType = (UnknownType) type;
      uType.setZName(ZUtils.assertZName(call));
      
      // post checking ?      
      if (!addedPostChecking)
      {
        paraErrors().add(term);      
        //addAction4PostCheck(getCurrentActionName());
        addedPostChecking = true;
      }
      //else  TODO: CHECK this part in manuelas code
      //{
      //  // tratamento especial para o caso de chamada recursiva
      //  List<NameTypePair> params = localCircTypeEnv().getActionInfo(actionDecl).getParams();
      //  // chama um método auxiliar que irá verificar se a chamada está correta
      //  checkCallAction(term, params);
      //}
    }
    
    if (type instanceof GenericType)
    {
      assert false : "TODO: generic calls? actions can't be generic, actually? or can thouhj gen formals from process?";
       if (!isPending())
       {
          
       }
       else
       {
          
       }
    }   
    
    // if the name is of a declared action type
    if (type instanceof ActionType)
    {
      ActionType aType = (ActionType)type;
      ActionSignature aSig = aType.getActionSignature();
      
      // if the signature refers to the call name, we are on
      if (ZUtils.namesEqual(call, aSig.getActionName()))
      {
        ZExprList actuals = term.getZExprList();
        List<NameTypePair> resolvedFormals = aSig.getFormalParams().getNameTypePair();                
                
        checkCallParameters(term, resolvedFormals, actuals);
        
      }
      // otherwise this is a awkward (type checker protocol) error. (?)
      else
      {
        Object [] params = { getCurrentProcessName(), getCurrentActionName() };
        error(term, ErrorMessage.IS_NOT_ACTION_NAME, params);       
      }            
    }        
    
    // calls have empty signatures.
    ActionSignature actionSignature = factory().createEmptyActionSignature();
    addActionSignatureAnn(term, actionSignature);
    
    return actionSignature;
  }
  
  /**
   * Forward command checking to the appropriate checker. This links C.12 with C.17.
   *
   *@law C.12.5
   */
  @Override
  public ActionSignature visitCircusCommand(CircusCommand term)
  {
    return term.accept(commandChecker());
  }  

  /**
   * Returns an empty action signature. It covers Skip, Stop, and Chaos.
   *
   *@law C.12.6, C.12.7, C.12.8
   */  
  // Action ::= Skip | Stop | Chaos
  public ActionSignature visitBasicAction(BasicAction term)
  {    
    checkActionParaScope(term, null);
    
    // \Gamma \rhd Skip | Stop | Chaos : Action 
    ActionSignature actionSignature = factory().createEmptyActionSignature();
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
      {                    /* old name ok          old name bad */
        /* new name ok  */  { SubstResolution.Go,  SubstResolution.Old },  
        /* new name bad */  { SubstResolution.New, SubstResolution.Both } 
      };
  
  /**
   *@law C.12.9
   */
  // Action ::= Action[N+ := N+]  // TODO!
  public ActionSignature visitSubstitutionAction(SubstitutionAction term)
  { 
    checkActionParaScope(term, null);
           
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
      
      assert false : "TODO";
      // retrieve the resolution from the valid subsitution list
      // TODO: DECISION: do not stop in case of error, but report it; or stop it?
      resolution = null; //SUBST_MATRIX[(isLocalVar(newName) ? 1 : 0)]
                         //            [(isLocalVar(oldName) ? 1 : 0)];        
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
         //error(term, ErrorMessage.NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION, params);                     
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
    checkActionParaScope(term, null);
    
    // enter the scope for input fields
    typeEnv().enterScope();
    
    // typecheck the communication part returning a list of name type pairs
    // it returns the input variables that need to be declared.
    // * calculate (VarsC c \Gamma)
    List<NameTypePair> comSig = term.getCommunication().accept(commChecker());    
    List<NameTypePair> inputVars = ((CommunicationChecker)commChecker()).filterInputs(comSig); 
    
    // Adds input variables into S1. The oplus at the signature level is implemented down below.
    // * create \Gamma' = (\Gamma \oplus (VarsC c \Gamma)) 
    // 
    // NOTE: variables should be added locally at the input field 
    //addLocalVars(inputVars);
    
    // type check given action in scope enriched with input variables
    // * checks \Gamma' \rhd a : Action
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());
    
    // updates the local variable signature for the prefixed action.
    actionSignature.getLocalVars().getNameTypePair().addAll(0, inputVars);
    
    // should contain the communication expressions!
    actionSignature.getUsedCommunications().add(0, term.getCommunication());    
    
    // close input variables scope after analysing the entailing action
    typeEnv().exitScope();
 
    addActionSignatureAnn(term, actionSignature);    
    return actionSignature;
  }
  
  /**
   * First checks the predicate in the guard, where possible partial evaluation
   * is considered, and then checkes the guarded action itself.
   * 
   *@law C.12.11
   */
  // Action ::= Predicate & Action  
  @Override
  public ActionSignature visitGuardedAction(GuardedAction term)
  {
    checkActionParaScope(term, null);
    
    Pred pred = term.getPred();
    UResult solved = pred.accept(predChecker());
    
    if (solved.equals(UResult.PARTIAL))
    {
      pred.accept(predChecker());
    }
    
    ActionSignature signature = term.getCircusAction().accept(actionChecker());
    addActionSignatureAnn(term, signature);
    
    return signature;
  }

  /**
   ** <p>
   * This method implements typechecking for sequential composition, internal
   * and external choice, and interleaved actions without name sets.
   * </p>
   * <p>
   * Check the action scope, then check each side is type correct. 
   * The collected signature is then joined to form this action signature.
   * Action signatures from trees dynamically generated (i.e., not by the parser)
   * should be carefull with action signature joining restrictions
   * (see {@link Checker#joinActionSignature(ActionSignature, ActionSignature) joinActionSignature}).
   * </p>
   *@law C.12.12, C.12.13, C.12.14, C.12.15
   */
  @Override
  public ActionSignature visitAction2(Action2 term)
  {
    // check within an action paragraph scope.
    checkActionParaScope(term, null);    
    
    // check each side
    ActionSignature actionSigL = term.getLeftAction().accept(actionChecker());
    ActionSignature actionSigR = term.getRightAction().accept(actionChecker());    
    
    // join the signatures, if possible (i.e. parsed specs shall always be).    
    ActionSignature result = joinActionSignature(term, actionSigL, actionSigR);    
    
    // annotate the term with given signature.
    addActionSignatureAnn(term, result);
    
    return result;
  }    
  
  protected NameSetType typeCheckNameSet(NameSet term)
  { 
    NameSetType result = (NameSetType)term.accept(exprChecker());
    
    assert false : "sort out name set and channel set update within action signature";
    
    //typeEnv().addUsedNameSets(...);
    
    return result;
  }
  
  protected ChannelSetType typeCheckChannelSet(ChannelSet term)
  {
    // TODO: CHECK: on-the-fly channel sets could be added latter? i.e. those built without channelsetpara
    ChannelSetType result = (ChannelSetType)term.accept(exprChecker());
    
    assert false : "sort out name set and channel set update within action signature";
    // adicionando os canais usados...
    //localCircTypeEnv().addUsedChans(result.getChannels().getNameTypePair());
    //typeEnv().addUsedChannelSets(...);
    
    return result;
  }
    
  /**
   * Partial.
   *@law C.12.16
   */
  public ActionSignature visitInterleaveAction(InterleaveAction term)
  {    
    // check the name sets
    typeCheckNameSet(term.getLeftNameSet());
    typeCheckNameSet(term.getRightNameSet());
    
    // check each side
    ActionSignature actionSignature = visitAction2(term);
    addActionSignatureAnn(term, actionSignature);    
    return actionSignature;
  }
  
  /**
   * Partial.
   *@law C.12.17
   */
  public ActionSignature visitParallelAction(ParallelAction term)
  {
    // check the channel and name sets
    typeCheckChannelSet(term.getChannelSet());
    typeCheckNameSet(term.getLeftNameSet());
    typeCheckNameSet(term.getRightNameSet());    
    
    ActionSignature actionSignature = visitAction2(term);
    addActionSignatureAnn(term, actionSignature);
    
    return actionSignature;
  }
  
  /**
   * Auxiliary method used by other visitors. Not directly implementing any
   * Action1, like Action2 directly implements ExtChoice, for instance.
   */
  public ActionSignature visitAction1(Action1 term)
  {
    // check within an action paragraph scope.
    checkActionParaScope(term, null);    
    
    // check the action itself and add signature
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());    
    addActionSignatureAnn(term, actionSignature);
    return actionSignature;
    
  }
  
  /**
   * Typechecks the channel set and the inner action, checking both action and
   * process scopes. Creates and returns a signature containing the used 
   * channel set.
   *
   *@law C.12.18
   */
  public ActionSignature visitHideAction(HideAction term)
  {
    typeCheckChannelSet(term.getChannelSet());
    
    ChannelSetType typeCS = (ChannelSetType)term.getChannelSet().accept(exprChecker());
    
    ActionSignature actionSignature = visitAction1(term);
    addActionSignatureAnn(term, actionSignature);
    
    return actionSignature;
  }
    
//  //ok - verificado em 15/09/2005 às 17:02
////  public Object visitActionD(ActionD term)
////  { // Loop!      
////    return term.accept(actionChecker());
////  }
//  
//  // Action ::= \mu N @ Action
//  //ok - verificado em 15/09/2005 às 17:03
//  public ActionSignature visitMuAction(MuAction term)
//  {
//    DeclName name = term.getDeclName();
//    CircusAction action = term.getCircusAction();
//    
//    addMuAction(name);
//    ActionSignature signature = action.accept(actionChecker());
//    removeMuAction(name);
//    
//    addActionSignatureAnn(term, signature);
//    
//    return signature;
//  }
//
//  
//  
//  
//  
//  //ok - verificado em 15/09/2005 às 17:47
//  public ActionSignature visitActionIte(ActionIte term)
//  {  
//    ZDeclList decs = term.getZDeclList();
//    CircusAction action = term.getCircusAction();
//
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    List<Object> paramsError = new ArrayList<Object>();
//    paramsError.add(assertZDeclName(currentAction()).getWord());
//    paramsError.add(assertZDeclName(currentProcess()).getWord());
//
//    for(Decl d : decs) {
//      if (!(d instanceof VarDecl))
//          throw new UnsupportedOperationException("Iterated actions accept only VarDecl!");
//      VarDecl dec = (VarDecl)d;
//      boolean declOK = false;
//      if(dec.getExpr() instanceof SetExpr) {
//        declOK = true;
//      }
//      else if(dec.getExpr() instanceof ApplExpr) {
//        ApplExpr applExpr = (ApplExpr)dec.getExpr();
//        if(applExpr.getLeftExpr() instanceof RefExpr) {
//          if(((RefExpr)applExpr.getLeftExpr()).getZRefName().getWord().equals(ZString.ARG_TOK + ".." + ZString.ARG_TOK)) {
//            declOK = true;
//          }
//        }
//      }
//      List<NameTypePair> pairs = (List<NameTypePair>)dec.accept(declChecker());
//      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_VAR_IN_ACTION_ITE, paramsError);
//      if(!declOK) {
//        Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord()};
//        error(term, ErrorMessage.INFINITY_VALUES_IN_ACTION_ITE, params);
//        break;
//      }
//    }
//    typeEnv().enterScope();
//
//    typeEnv().add(allPairs);
//    ActionSignature actionSig = action.accept(actionChecker());
//    ActionSignature actionSignature = cloneActionSignature(actionSig);
//    Signature sig = factory().createSignature(allPairs);
//    actionSignature.setLocalVarsSignature(sig);
//    
//    typeEnv().exitScope();
//    // TODO: added for consistency.
//    addActionSignatureAnn(term,  actionSignature);
//
//    return actionSignature;
//  }
//
//  // Action ::= Declaration @ Action
//  //ok - verificado em 15/09/2005 às 18:12
//  public ActionSignature visitParamAction(ParamAction term)
//  {
//  
//// FROM old call action.    
////    if(assertZDeclName(actionDecl).getWord().startsWith("$$implicitAction_")) {
////      // pegar da lista de ações implícitos, fazer a verificação e incluir no
////      // TypeEnv!!
////      List<ActionPara> implicitActions = (List<ActionPara>)localCircTypeEnv().getOnTheFlyActions();
////      for(ActionPara implicitAction : implicitActions) {
////        if(compareDeclName(actionDecl, implicitAction.getDeclName(), true)) {
////          Signature implicitActionSig = implicitAction.accept(paraChecker());
////        }
////      }
////    }
////    
////    // verifica se é uma chamada a uma ação mu
////    if(isMuAction(actionDecl)) {
////      if(!(term.getZExprList().isEmpty())) {
////        Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), assertZDeclName(actionDecl).getWord()};
////        error(term, ErrorMessage.MU_ACTION_CALL_ERROR, params);
////      }
////    }
//    
//    ZDeclList decls = term.getZDeclList();
//    CircusAction action = term.getCircusAction();
//
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    List<Object> paramsError = new ArrayList<Object>();
//    paramsError.add(assertZDeclName(currentAction()).getWord());
//    paramsError.add(assertZDeclName(currentProcess()).getWord());
//
//    for(Decl d : decls) {
//      if (!(d instanceof VarDecl))
//        throw new UnsupportedOperationException("Parameterised actions accept only VarDecl!");
//      VarDecl decl = (VarDecl)d;
//      List<NameTypePair> pairs = decl.accept(declChecker());
//      allPairs = checkDecls(allPairs, pairs, term, ErrorMessage.REDECLARED_PARAM_IN_ACTION, paramsError);
//    }
//    
//    // atualiza informações sobre a ação
//    ActionInfo actionInfo = localCircTypeEnv().getActionInfo(currentAction());
//    actionInfo.setIsParam(true);
//    actionInfo.setParams(allPairs);
//
//    typeEnv().enterScope();
//    
//    typeEnv().add(allPairs);    
//    ActionSignature actionSig = action.accept(actionChecker());
//    ActionSignature actionSignature = cloneActionSignature(actionSig);
//    Signature varsSig = factory().createSignature(allPairs);
//    actionSignature.setParams(varsSig);
//    typeEnv().exitScope();
//    
//    addActionSignatureAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//  
//  // existe ?!?
//  //ok - verificado em 15/09/2005 às 17:50
////  public Object visitParActionIte(ParActionIte term)
////  {
////    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
////    addActionSignatureAnn(term, actionSignature);
////    
////    return actionSignature;
////  }
//  
//  // Action ::= \Extchoice Declaration @ Action
//  //ok - verificado em 15/09/2005 às 17:50
////  public Object visitExtChoiceActionIte(ExtChoiceActionIte term)
////  {
////    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
////    addActionSignatureAnn(term, actionSignature);
////    
////    return actionSignature;
////  }
////  
////  // Action ::= \Intchoice Declaration @ Action
////  //ok - verificado em 15/09/2005 às 17:50
////  public Object visitIntChoiceActionIte(IntChoiceActionIte term)
////  {
////    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
////    addActionSignatureAnn(term, actionSignature);
////    
////    return actionSignature;
////  }
////
////  // Action ::= \Semi Declaration @ Action
////  //ok - verificado em 15/09/2005 às 17:50
////  public Object visitSeqActionIte(SeqActionIte term)
////  {
////    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
////    addActionSignatureAnn(term, actionSignature);
////    
////    return actionSignature;
////  }
//
//  // Action ::= \Parallel Declaration @ |[NSExpression | CSExpression]| Action
//  // Action ::= \Parallel Declaration @ |[CSExpression]| Action
//  //ok - verificado em 15/09/2005 às 17:52
//  public ActionSignature visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//
//    NameSetType typeNS = (NameSetType)term.getNameSet().accept(exprChecker());
//
//    ActionSignature actionSignature = visitActionIte(term);
//    //addActionSignatureAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//
//  // Action ::= \Interleave Declaration @ Action
//  // Action ::= \Interleave Declaration @ ||[NSExpression]|| Action
//  //ok - verificado em 15/09/2005 às 17:53
//  public ActionSignature visitInterleaveActionIte(InterleaveActionIte term)
//  {
//    NameSetType typeNS = (NameSetType)term.getNameSet().accept(exprChecker());
//    
//    ActionSignature actionSignature = visitActionIte(term);
//    //addActionSignatureAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//
//  // Action ::= |[CSExpression]| Declaration @ |[NSExpression]| Action
//  // Action ::= |[CSExpression]| Declaration @ Action
//  //ok - verificado em 15/09/2005 às 17:52
//  public ActionSignature visitParallelActionIte(ParallelActionIte term)
//  {
//    ChanSetType typeCS = (ChanSetType)term.getChannelSet().accept(exprChecker());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(typeCS.getChannels().getNameTypePair());
//    //
//
//    NameSetType typeNS = (NameSetType)term.getNameSet().accept(exprChecker());
//
//    ActionSignature actionSignature = (ActionSignature)visitActionIte(term);
//    addActionSignatureAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
//  
//  // Action ::= Action \extchoice Action
//  //ok - verificado em 15/09/2005 às 18:00
////  public Object visitExtChoiceAction(ExtChoiceAction term)
////  {
////    ActionSignature actionSignature = (ActionSignature)visitAction2(term);
////    addActionSignatureAnn(term, actionSignature);
////    
////    return actionSignature;
////  }
////
////  // Action ::= Action \intchoice Action
////  //ok - verificado em 15/09/2005 às 18:01
////  public Object visitIntChoiceAction(IntChoiceAction term)
////  {
////    ActionSignature actionSignature = (ActionSignature)visitAction2(term);
////    addActionSignatureAnn(term, actionSignature);
////    
////    return actionSignature;
////  }
////
////  // Action ::= Action ; Action
////  //ok - verificado em 15/09/2005 às 18:01
////  public Object visitSeqAction(SeqAction term)
////  {
////    ActionSignature actionSignature = (ActionSignature)visitAction2(term);
////    addActionSignatureAnn(term, actionSignature);
////    
////    return actionSignature;
////  }
////  
////  //existe?!?
////  //ok - verificado em 15/09/2005 às 18:02
////  public Object visitParAction(ParAction term)
////  {
////    return visitAction2(term);
////  }
//  
//
//  // Action ::= Action |[CSExpression || CSExpression]| Action
//  // Action ::= Action |[NSExpression | CSExpression || CSExpression | NSExpression]| Action
//  //ok - verificado em 15/09/2005 às 18:
//  public ActionSignature visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
//  {
//    List<NameTypePair> allPairs = new ArrayList<NameTypePair>();
//    ChanSetType typeCSL = (ChanSetType)term.getLeftAlpha().accept(exprChecker());
//    ChanSetType typeCSR = (ChanSetType)term.getRightAlpha().accept(exprChecker());
//    allPairs.addAll(typeCSL.getChannels().getNameTypePair());
//    allPairs.addAll(typeCSR.getChannels().getNameTypePair());
//    // adicionando os canais usados...
//    localCircTypeEnv().addUsedChans(allPairs);
//    //
//    
//   // NameSetType typeNSL = (NameSetType)term.getLeftNameSet().accept(exprChecker());
//   // NameSetType typeNSR = (NameSetType)term.getRightNameSet().accept(exprChecker());
//
//    term.getLeftNameSet().accept(exprChecker());
//    term.getRightNameSet().accept(exprChecker());
//    ActionSignature actionSignature = visitAction2(term);
//    //addActionSignatureAnn(term, actionSignature);
//    
//    return actionSignature;
//  }
}
