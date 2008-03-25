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
import java.util.ListIterator;
import net.sourceforge.czt.circus.ast.Action2;
import net.sourceforge.czt.circus.ast.ActionD;
import net.sourceforge.czt.circus.ast.ActionIte;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelAction;
import net.sourceforge.czt.circus.ast.BasicAction;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusCommand;
import net.sourceforge.czt.circus.ast.GuardedAction;
import net.sourceforge.czt.circus.ast.HideAction;
import net.sourceforge.czt.circus.ast.InterleaveAction;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ParAction;
import net.sourceforge.czt.circus.ast.ParallelAction;
import net.sourceforge.czt.circus.ast.ParamAction;
import net.sourceforge.czt.circus.ast.PrefixingAction;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.SubstitutionAction;
import net.sourceforge.czt.circus.ast.ParActionIte;
import net.sourceforge.czt.circus.ast.ParallelActionIte;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelActionIte;
import net.sourceforge.czt.circus.visitor.Action2Visitor;
import net.sourceforge.czt.circus.visitor.ActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.BasicActionVisitor;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.CircusCommandVisitor;
import net.sourceforge.czt.circus.visitor.GuardedActionVisitor;
import net.sourceforge.czt.circus.visitor.HideActionVisitor;
import net.sourceforge.czt.circus.visitor.InterleaveActionVisitor;
import net.sourceforge.czt.circus.visitor.MuActionVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.ParamActionVisitor;
import net.sourceforge.czt.circus.visitor.ParActionIteVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.PrefixingActionVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus.visitor.SubstitutionActionVisitor;
import net.sourceforge.czt.typecheck.circus.ErrorAnn;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.z.ast.GenericType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZRenameList;
import net.sourceforge.czt.z.util.ZUtils;

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
 */
public class ActionChecker
  extends Checker<ActionSignature>
  implements  
  ParamActionVisitor<ActionSignature>,                  //  C.12.1, C.12.2, C.16.1
  SchExprActionVisitor<ActionSignature>,                //  C.12.3
  CallActionVisitor<ActionSignature>,                   //  C.12.4, C.12.19, C.12.20, C.17.6
  CircusCommandVisitor<ActionSignature>,                //  C.12.5
  BasicActionVisitor<ActionSignature>,
  //SkipActionVisitor,                                      C.12.6
  //StopActionVisitor,                                      C.12.7
  //ChaosActionVisitor,                                     C.12.8
  SubstitutionActionVisitor<ActionSignature>,           //  C.12.9     
  PrefixingActionVisitor<ActionSignature>,              //  C.12.10
  GuardedActionVisitor<ActionSignature>,                //  C.12.11
  Action2Visitor<ActionSignature>,
  //SeqActionVisitor,                                       C.12.12
  //ExtChoiceActionVisitor,                                 C.12.13
  //IntChoiceActionVisitor,                                 C.12.14  
  InterleaveActionVisitor<ActionSignature>,             //  C.12.15, C.12.16
  ParallelActionVisitor<ActionSignature>,               //  C.12.17
  AlphabetisedParallelActionVisitor<ActionSignature>,   //  C.12.17-2
  HideActionVisitor<ActionSignature>,                   //  C.12.18
  MuActionVisitor<ActionSignature>,                     //  C.12.21
  ActionIteVisitor<ActionSignature>,                      
  //SeqActionIteVisitor,                                    C.12.22
  //ExtChoiceActionIteVisitor,                              C.12.23
  //IntChoiceActionIteVisitor,                              C.12.24  
  ParActionIteVisitor<ActionSignature>,                 //  C.12.25, C.12.26
  ParallelActionIteVisitor<ActionSignature>,            //  C.12.27
  AlphabetisedParallelActionIteVisitor<ActionSignature> //  C.12.27-2
  
{
  /** Creates a new instance of ActionChecker */
  public ActionChecker(TypeChecker typeChecker)
  {
    super(typeChecker);   
  }
  
  /**
   * This general method typechecks all parameterised action. It covers ParamAction,
   * and all ActionIte.
   * It checks the declared parameters (possibly including generic types from 
   * the process this action belongs) for duplicated names and type mismatches, 
   * putting then into scope. Finally, it typechecks the declaring action with 
   * the parameters in scope adding them to the resulting action signature with 
   * the formal parameters set. If qualified declarations are allowed and present,
   * state variables are also added to the current scope and the resulting action 
   * signature.
   */
  protected ActionSignature typeCheckActionD(ActionD term, 
    boolean considerFiniteness, boolean allowQualifiedDecl)
  {
    checkActionParaScope(term, null);
    
    // type check the list of declared parameters - it returns the
    // formal parameters signature already considering generics
    List<NameTypePair> gParams = typeCheckCircusDeclList(
      term, term.getZDeclList(), considerFiniteness,
      allowQualifiedDecl, ErrorMessage.INVALID_DECL_IN_ACTIONITE, 
      factory().<Object>list(getCurrentProcessName(), getCurrentActionName()));

    // put the declared parameters into the action's scope
    typeEnv().enterScope();
    
    // in general the signature of local variables is just
    // the formal parameters - unless this is a parameterised
    // command, in which case more state variables are added.
    List<NameTypePair> allVars = gParams;
    
    // if this is a ParamAction that is a CircusCommand
    // then we need to add state variables as well.
    if (allowQualifiedDecl)
    {
      // update the local variables gParams with the new set of state variables
      allVars = addStateVars(gParams);
    }
    // otherwise, this is either a ParamAction that is not 
    // a command or some iterated action
    else
    {
      typeEnv().add(gParams);
    }
    
    // check the inner action now with the parameters in scope
    CircusAction action = term.getCircusAction();
    ActionSignature actionSignature = action.accept(actionChecker());
    
    // clone the signature
    //ActionSignature actionDSig = (ActionSignature)actionSignature.create(actionSignature.getChildren());
    ActionSignature actionDSig = (ActionSignature)factory().deepCloneTerm(actionSignature);
    
    // if nesting is present, raise an error - it isn't allowed
    // unless this is call action, in which case parameters may be present
    // !(!actionDSig.getFormalParams().getNameTypePair().isEmpty() => action instanceof CallAction)    
    if (!(action instanceof CallAction) && 
        !actionDSig.getFormalParams().getNameTypePair().isEmpty())
    {
      Object[] params = {
        getCurrentProcessName(),
        getCurrentActionName()        
      };
      error(term, ErrorMessage.NESTED_FORMAL_PARAMS_IN_ACTION, params);
    }
    
    // updates the formal parameters signature with gParams     
    actionDSig.setFormalParams(factory().createSignature(gParams));
        
    // updates the local variable signature with allVars - duplicates are fine(?) TODO:CHECK
    actionDSig.getLocalVars().getNameTypePair().addAll(0, allVars);
    
    typeEnv().exitScope();            
    
    return actionDSig;
  }  
  
  /**
   * Typechecks all iterated actions. It performs the general protocol for
   * actions with declaring parameters (ActionD), and then make sure the 
   * types within the declarations are finite.
   * @param term
   * @return
   */
  protected ActionSignature typeCheckActionIte(ActionIte term)
  {    
    // all ActionIte are typechecked just liked ActionD
    // no qualified declaration is allowed - only param commands have them
    // and types of declarations ought to be finite
    ActionSignature actionSignature = typeCheckActionD(term, 
      true, /* considerFiniteness */
      false /* allowQualifiedDecl */);
    
    // iterated actions do not have parameters
    actionSignature.getFormalParams().getNameTypePair().clear();
    return actionSignature;
  }
  
  protected List<Object> getChannelSetErrorParams()
  {
    // within the ActionChecker, it must be for an action use 
    // rather than at declaration point.
    List<Object> errorParams = factory().list();
    errorParams.add("process");
    errorParams.add(getCurrentProcessName().toString() +
        "\n\tAction...: " + getCurrentActionName().toString());
    return errorParams;    
  }
  
  
  protected List<Object> getNameSetErrorParams()
  {
    // within the ActionChecker, it must be for an action use 
    // rather than at declaration point.      
    List<Object> params = factory().list();
    params.add(getCurrentProcessName());
    params.add("action");
    params.add(getCurrentActionName());      
    return params;
  }
  
  protected ActionSignature typeCheckParActionIte(ParActionIte term, ChannelSet cs)
  {
    // type check name set and channel set
    NameSet ns = term.getNameSet();
    typeCheckNameSet(ns, getNameSetErrorParams());
    
    // null for interleaving
    if (cs != null)
    {
      ChannelSetType cst = typeCheckChannelSet(cs, getChannelSetErrorParams());        
    }
    
    // typecheck inner action
    ActionSignature actionSignature = typeCheckActionIte(term);
    
    // clone signature and update name sets used
    ActionSignature actionDSig = (ActionSignature)factory().deepCloneTerm(actionSignature);    
    actionDSig.getUsedNameSets().add(0, ns);
    
    // null for interleaving
    if (cs != null)
    {
      actionDSig.getUsedChannelSets().add(0, cs);
    }
    
    return actionDSig;
  }
  
  protected ActionSignature typeCheckParAction(ParAction term, List<ChannelSet> channelSets)
  {
    // check the name sets
    NameSet nsL = term.getLeftNameSet();
    NameSet nsR = term.getRightNameSet();  
    List<Object> errorParams = getNameSetErrorParams();
    typeCheckNameSet(nsL, errorParams);
    typeCheckNameSet(nsR, errorParams);
    
    // typecheck inner actions
    ActionSignature actionSignature = visitAction2(term);
        
    // clone signature and update name sets used - L first; R next
    // i.e., add the last one first at the head then the next, gives this order
    ActionSignature actionDSig = (ActionSignature)factory().deepCloneTerm(actionSignature);        
    actionDSig.getUsedNameSets().add(0, nsR);
    actionDSig.getUsedNameSets().add(0, nsL);
       
    
    // within the ActionChecker, it must be for an action use 
    // rather than at declaration point.
    errorParams = getChannelSetErrorParams();
    
    // check the channel sets
    for(ListIterator<ChannelSet> lit = 
        channelSets.listIterator(channelSets.size()); 
        lit.hasPrevious() ; ) 
    {
      ChannelSet cs = lit.previous();
      ChannelSetType cst = typeCheckChannelSet(cs, errorParams);      
      actionDSig.getUsedChannelSets().add(0, cs);
    }    
        
    return actionDSig;
  }
  
  /**
   * Typechecks a parameterised action. It checks the declared parameters
   * (possibly including generic types from the process this action belongs) for 
   * duplicated names and type mismatches, putting then into scope. Finally,
   * it typechecks the declaring action with the parameters in scope adding them
   * to the resulting action signature.
   *
   *@law C.12.1, C.12.2, C.16.1
   */
  public ActionSignature visitParamAction(ParamAction term)
  {     
    // commands allow qualified declarations    
    // and types of declarations do not need to be finite
    ActionSignature actionDSig = typeCheckActionD(term, 
      false,                /* considerFiniteness */
      term.isParamCommand() /* allowQualifiedDecl */);
    addActionSignatureAnn(term, actionDSig);
    return actionDSig;
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

    // type check the schema expressions    
    Type type = term.getExpr().accept(exprChecker());
    
    // create an empty signature
    ActionSignature actionSignature = factory().createEmptyActionSignature();

    SchemaType schType = referenceToSchema(type);
    if (schType != null)
    {  
      // checks the schema expression adding local variables to the signature.
      List<ErrorAnn> varScopeErrors = checkStateVarsScopeInSchExprAction(term, schType);
      
      // if no errors were found, add local vars to the signature
      if (varScopeErrors.isEmpty())
      {        
        actionSignature.getLocalVars().getNameTypePair().addAll(schType.getSignature().getNameTypePair());
      }
      // otherwise raise the errors
      else
      {
        raiseErrors(term, varScopeErrors);      
      }
    }
    // not a schema expression in a schema expression action
    else
    {
      Object[] params = {getCurrentProcessName(), getCurrentActionName(), term, type };
      error(term, ErrorMessage.SCHEXPR_ACTION_WITHOUT_SCHEXPR, params);
    }
    
    //TODO: add StateUpdate!
    
    // annotate the term with the collected signature
    addActionSignatureAnn(term, actionSignature);

    return actionSignature;
  }

  /**
   * <p>
   * This visiting method represents all forms of action call. They are:
   * simple calls A, parameterised calls A(el), or on-the-fly calls, 
   * which can be either simple or parameterised. The parser is responsible
   * for making on-the-fly actions implicitly declared (with a special internal
   * name, see {@link net.sourceforge.czt.circus.ast.util.CircusString}). The 
   * action declaration for the on-the-fly action also has a OnTheFlyDefAnn.
   * </p>
   * <p>
   * Tools building actions on-the-fly dynamically MUST follow the protocol.
   * The parser enforces this by declaring the action right before its call takes place.
   * Therefore, typechecking well-formed terms assume on-the-fly actions are just
   * treated as calls. This way, the type rule for C.12.20 is slightly simplified
   * because there is no need to check for the action being declared on-the-fly here
   * (i.e., it will be checked earlier on the basic process ZParaList anyway).
   * </p>
   * <p>
   * Thus, this type rule covers action calls (with or without parameters), 
   * mu action action calls, on-the-fly actions, and on-the-fly parameterised 
   * commands.
   * </p>
   *@law C.12.4, C.12.19, C.12.20, C.17.6
   */  
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

    // see if this call has already been type checked
    Type type = getType2FromAnns(call);
    if (type instanceof UnknownType)
    {
      type = getLocalType(call); //getGlobalType(call);
    }

    boolean addedPostChecking = false;
    //add this reference for post checking --- this is CZT's approach
    if ((type instanceof UnknownType) && !GlobalDefs.containsObject(paraErrors(), term))
    {
      //if (!ZUtils.namesEqual(getCurrentActionName(), call))
      //{
        paraErrors().add(term);
        addedPostChecking = true; // see this flag below.
      //}
    }

    //if this is undeclared, create an unknown type with this CallAction
    //i.e., getGlobalType(call) may add a UndeclaredAdd to call
    Object undecAnn = call.getAnn(UndeclaredAnn.class);

    //if we are using name IDs, then read the type off the name if it
    //is not in the type environment    
    // TODO: CHECK: ask Tim, this is a known name then?
    if (undecAnn != null && sectTypeEnv().getUseNameIds())
    {
      type = GlobalDefs.getTypeFromAnns(term);
      if (!(type instanceof UnknownType))
      {
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

      // add post checking if not there already
      addedPostChecking = true;
      if (!GlobalDefs.containsObject(paraErrors(), term))
      {
        paraErrors().add(term);       
      }
    }

    if (type instanceof GenericType)
    {
      Object[] params = { getCurrentProcessName(), getCurrentActionName(), call };
      error(term, ErrorMessage.ACTION_CALL_GENTYPE, params);
    }

    List<ErrorAnn> callErrors = checkCallActionConsistency(GlobalDefs.unwrapType(type), term);    
    if (addedPostChecking)
    { 
      appendCallErrors(call, callErrors);      
    }
    else
    {
      raiseErrors(term, callErrors);
    }
    
    // calls have the signature of its type or empty if invalid.    
    // yet, the result signature is always empty, so that it does not 
    // contaminate outer signatures being formed.
    ActionSignature resultSignature = factory().createEmptyActionSignature();
    ActionSignature actionSignature = factory().createEmptyActionSignature();
        
    // if action type, then clone the call signature
    if (type instanceof ActionType)
    {
      actionSignature = factory().deepCloneTerm(GlobalDefs.actionType(type).getActionSignature());
    }
    // otherwise, see if this is a call for SchExpr action without special brackets, 
    // but only if no errors were found by the consistency method
    else if (callErrors.isEmpty())
    {      
      SchemaType schType = referenceToSchema(type);
      if (schType != null)
      {
        actionSignature.getLocalVars().getNameTypePair().addAll(schType.getSignature().getNameTypePair());
      }
      //actionSignature.setActionName(call);
    }
    
    // update the term action signature as one calculated 
    addActionSignatureAnn(term, actionSignature);
    resultSignature.setActionName(getCurrentActionName());    
    if (isWithinMuActionScope())
    {
      resultSignature.setSignatureOfMuAction(true);
    }
    
    // return the empty action signature
    return resultSignature;
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
  private enum SubstResolution
  {

    Go, Old, New, Both
  }
  ;

  private static final  SubstResolution    
      [][] SUBST_MATRIX = 
      {                    /* old name ok          old name bad */
        /* new name ok  */  { SubstResolution.Go,  SubstResolution.Old },  
        /* new name bad */  { SubstResolution.New, SubstResolution.Both } 
      }
  ;
  
  /**
   *@law C.12.9
   */ 
  public ActionSignature visitSubstitutionAction(SubstitutionAction term)
  { 
    checkActionParaScope(term, null);

    // the parser enforces              #ln1 = #ln2
    ZRenameList zrl = term.getZRenameList();
    int i = 1;
    SubstResolution resolution;
    boolean hasError = false;
    for (NewOldPair nop : zrl)
    {
      // check both ln1 and ln2 are known local variables,   
      // (Into lnX \dom(\Gamma.localVars)) for X= {1,2}        
      ZName newName = nop.getZDeclName();
      ZName oldName = nop.getZRefName();
      Type oldType = getLocalType(oldName);
      Type newType = getLocalType(newName);
      
      // TODO: CHECK: what about substitution to global names?
      // check if given names are local variable names - i.e., within the typeEnv() current scope
      resolution = SUBST_MATRIX[(isLocalVar(newName) ? 1 : 0)][(isLocalVar(oldName) ? 1 : 0)];                    
      if (resolution.equals(SubstResolution.Go))
      {        
        Type2 expectedU = GlobalDefs.unwrapType(oldType);
        Type2 foundU = GlobalDefs.unwrapType(newType);
        
        if (!unify(foundU, expectedU).equals(UResult.SUCC)) 
        {
          Object [] params = { getCurrentProcessName(), getCurrentActionName(), oldName, newName, i, expectedU, foundU };
          error(term, ErrorMessage.ACTION_SUBSTITUTION_DONT_UNIFY, params);          
        }
      }
      else
      {
        String name = "";        
        switch (resolution)
        {
          case New:
            name = newName.toString();
            break;
          case Old:
            name = oldName.toString();
            break;
          case Both:
            name = newName.toString() + " and " +
              oldName.toString();
            break;
        }
        Object[] params = { getCurrentProcessName(), getCurrentActionName(), name, i, resolution };
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
    checkActionParaScope(term, null);

    // enter the scope for input fields
    typeEnv().enterScope();

    // typecheck the communication part returning a list of name type pairs
    // it returns the input variables that need to be declared.
    // * calculate (VarsC c \Gamma)
    List<NameTypePair> comSig = term.getCommunication().accept(commChecker());
    List<NameTypePair> inputVars = ((CommunicationChecker) commChecker()).filterInputs(comSig);

    // Adds input variables into S1. The oplus at the signature level is implemented down below.
    // * create \Gamma' = (\Gamma \oplus (VarsC c \Gamma)) 
    // 
    // NOTE: variables should be added locally at the input field 
    //addStateVars(inputVars);

    // type check given action in scope enriched with input variables
    // * checks \Gamma' \rhd a : Action
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());

    // clone the signature.
    //ActionSignature prefixSignature = (ActionSignature)actionSignature.create(actionSignature.getChildren());
    ActionSignature prefixSignature = (ActionSignature)factory().deepCloneTerm(actionSignature);
    
    // updates the local variable signature for the prefixed action.
    prefixSignature.getLocalVars().getNameTypePair().addAll(0, inputVars);
    
    // add the channels used channels
    prefixSignature.getUsedChannels().getNameTypePair().add(0, commChecker().lastUsedChannelDecl());
      
    // add the communication expressions!
    prefixSignature.getUsedCommunications().add(0, term.getCommunication());

    // close input variables scope after analysing the entailing action
    typeEnv().exitScope();

    addActionSignatureAnn(term, prefixSignature);
    return prefixSignature;
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
    
    typeCheckPred(term, term.getPred());

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

  /**
   * Partial.
   *@law C.12.16
   */
  public ActionSignature visitInterleaveAction(InterleaveAction term)
  {
    ActionSignature actionDSig = typeCheckParAction(term, factory().<ChannelSet>list());    
    addActionSignatureAnn(term, actionDSig);
    return actionDSig;
  }

  /**   
   *@law C.12.17
   */
  public ActionSignature visitParallelAction(ParallelAction term)
  {    
    ActionSignature actionDSig = typeCheckParAction(term, factory().<ChannelSet>list(term.getChannelSet()));
    addActionSignatureAnn(term, actionDSig);
    return actionDSig;   
  }
  
  public ActionSignature visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
  {
    ActionSignature actionDSig = typeCheckParAction(term, factory().<ChannelSet>list(
      term.getLeftAlpha(), term.getRightAlpha()));
    addActionSignatureAnn(term, actionDSig);
    return actionDSig;  
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
    // check within an action paragraph scope.
    checkActionParaScope(term, null);

    ChannelSet cs = term.getChannelSet();
    ChannelSetType csType = typeCheckChannelSet(cs, getChannelSetErrorParams());

    // check the action itself and add signature
    ActionSignature actionSignature = term.getCircusAction().accept(actionChecker());
    
    // clone signature and update name sets used
    ActionSignature actionDSig = (ActionSignature)factory().deepCloneTerm(actionSignature);
    actionDSig.getUsedChannelSets().add(0, cs);
    
    // add signature to the term
    addActionSignatureAnn(term, actionDSig);

    return actionDSig;
  }

  /**
   * Puts the mu action name into scope with an empty action signature;
   * then make sure the action declaration 
   *
   *@law C.12.21
   */
  public ActionSignature visitMuAction(MuAction term)
  {
    Name aName = term.getName();
    CircusAction action = term.getCircusAction();
    
    // check within an action paragraph scope.
    checkActionParaScope(term, aName);

    // open scope for recursive variable
    typeEnv().enterScope();
    
    // add recursive variable to the type environment
    // the action type for the call just has an empty
    // signature, like CallAction does.
    ActionSignature aSig = factory().createInitialMuActionSignature(aName);
    ActionType aType = factory().createActionType(aSig);    
    NameTypePair recVarPair = factory().createNameTypePair(aName, aType);    
    typeEnv().add(recVarPair);
    
    setMuActionScope(true);
    
    // this action signature is set into "action" through the addActionSignatureAnn
    // method present in all other visitors. So, "action" already have the signature
    // annotation with "aName" associated with it.
    ActionSignature actionSignature = checkActionDecl(aName, action, term);

    setMuActionScope(false);
    
    // For the MuAction, the signature is the same, but updated 
    // with outer action name . TODO: check if we need a stacked environment here.
    //ActionSignature muSignature = factory().createActionSignature(null,
    //  actionSignature.getFormalParams(),
    //  actionSignature.getLocalVars(),
    //  actionSignature.getCommunicationList());
    ActionSignature muSignature = (ActionSignature)factory().deepCloneTerm(actionSignature);
    muSignature.setSignatureOfMuAction(true);
    
    // exit recursive variable scope
    typeEnv().exitScope();
    
    // update the action type for the call action
    aType.setActionSignature(muSignature);
    
    // add action type to CircusAction 
    addTypeAnn(action, aType);
    
    // update the mu signature with the action name.
    //muSignature.setActionName(aName);        
        
    // add the signature to the term
    addActionSignatureAnn(term, muSignature);    
    
    // check the action itself and add signature
    return muSignature;
  }
  
/**
   * 
   * @param term
   * @return
   * 
   * @law C.12.22, C.12.23, C.12.24
   */
  public ActionSignature visitActionIte(ActionIte term)
  {    
    ActionSignature actionDSig = typeCheckActionIte(term);
    addActionSignatureAnn(term, actionDSig);
    return actionDSig;    
  }
  
  /**
   * Interleaving 
   * @param term
   * @return
   * 
   * * @law C.12.25, C.12.26
   */
  public ActionSignature visitParActionIte(ParActionIte term)
  {     
    ActionSignature actionDSig = typeCheckParActionIte(term, null);    
    addActionSignatureAnn(term, actionDSig);
    return actionDSig;    
  }

  /**
   * 
   * @param term
   * @return
   * 
   * @law C.12.27
   */   
  public ActionSignature visitParallelActionIte(ParallelActionIte term)
  { 
    ActionSignature actionDSig = typeCheckParActionIte(term, term.getChannelSet());
    addActionSignatureAnn(term, actionDSig);    
    return actionDSig;
  }
  
  /**
   * 
   * @param term
   * @return
   * 
   * @law C.12.27-2
   */   
  public ActionSignature visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
  {
    ActionSignature actionDSig = typeCheckParActionIte(term, term.getChannelSet());
    addActionSignatureAnn(term, actionDSig);    
    return actionDSig;
  }  

//  // Action ::= Declaration @ Action
//  //ok - verificado em 15/09/2005 s 18:12
//  public ActionSignature visitParamAction(ParamAction term)
//  {
//  
//// FROM old call action.    
////    if(assertZDeclName(actionDecl).getWord().startsWith("$$implicitAction_")) {
////      // pegar da lista de acoes implicitos, fazer verificacao e incluir no TypeEnv!!
////      List<ActionPara> implicitActions = (List<ActionPara>)localCircTypeEnv().getOnTheFlyActions();
////      for(ActionPara implicitAction : implicitActions) {
////        if(compareDeclName(actionDecl, implicitAction.getDeclName(), true)) {
////          Signature implicitActionSig = implicitAction.accept(paraChecker());
////        }
////      }
////    }
////    
////    if(isMuAction(actionDecl)) {
////      if(!(term.getZExprList().isEmpty())) {
////        Object [] params = {assertZDeclName(currentAction()).getWord(), assertZDeclName(currentProcess()).getWord(), assertZDeclName(actionDecl).getWord()};
////        error(term, ErrorMessage.MU_ACTION_CALL_ERROR, params);
////      }
////    }
//    
//  }
//  
}
