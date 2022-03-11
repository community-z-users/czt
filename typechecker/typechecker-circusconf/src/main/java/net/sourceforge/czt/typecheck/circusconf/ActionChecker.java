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
package net.sourceforge.czt.typecheck.circusconf;

import java.util.List;
import java.util.ListIterator;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.Action2;
import net.sourceforge.czt.circus.ast.ActionD;
import net.sourceforge.czt.circus.ast.ActionIte;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelAction;
import net.sourceforge.czt.circus.ast.AlphabetisedParallelActionIte;
import net.sourceforge.czt.circus.ast.BasicAction;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusCommand;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.GuardedAction;
import net.sourceforge.czt.circus.ast.HideAction;
import net.sourceforge.czt.circus.ast.InterleaveAction;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.ParAction;
import net.sourceforge.czt.circus.ast.ParActionIte;
import net.sourceforge.czt.circus.ast.ParallelAction;
import net.sourceforge.czt.circus.ast.ParallelActionIte;
import net.sourceforge.czt.circus.ast.ParamAction;
import net.sourceforge.czt.circus.ast.PrefixingAction;
import net.sourceforge.czt.circus.ast.RenameAction;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.SubstitutionAction;
import net.sourceforge.czt.circus.visitor.Action2Visitor;
import net.sourceforge.czt.circus.visitor.ActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.AlphabetisedParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.BasicActionVisitor;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.CircusCommandVisitor;
import net.sourceforge.czt.circus.visitor.GuardedActionVisitor;
import net.sourceforge.czt.circus.visitor.HideActionVisitor;
import net.sourceforge.czt.circus.visitor.InterleaveActionVisitor;
import net.sourceforge.czt.circus.visitor.MuActionVisitor;
import net.sourceforge.czt.circus.visitor.ParActionIteVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionIteVisitor;
import net.sourceforge.czt.circus.visitor.ParallelActionVisitor;
import net.sourceforge.czt.circus.visitor.ParamActionVisitor;
import net.sourceforge.czt.circus.visitor.PrefixingActionVisitor;
import net.sourceforge.czt.circus.visitor.RenameActionVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus.visitor.SubstitutionActionVisitor;
import net.sourceforge.czt.typecheck.circus.CommunicationChecker;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GenericType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZRenameList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;

public class ActionChecker
  extends Checker<CircusCommunicationList>
  implements  
  ParamActionVisitor<CircusCommunicationList>,                  //  C.12.1, C.12.2, C.16.1
  SchExprActionVisitor<CircusCommunicationList>,                //  C.12.3
  CallActionVisitor<CircusCommunicationList>,                   //  C.12.4, C.12.19, C.12.20, C.17.6
  CircusCommandVisitor<CircusCommunicationList>,                //  C.12.5
  BasicActionVisitor<CircusCommunicationList>,
  //SkipActionVisitor,                                      C.12.6
  //StopActionVisitor,                                      C.12.7
  //ChaosActionVisitor,                                     C.12.8
  SubstitutionActionVisitor<CircusCommunicationList>,           //  C.12.9     
  PrefixingActionVisitor<CircusCommunicationList>,              //  C.12.10
  GuardedActionVisitor<CircusCommunicationList>,                //  C.12.11
  Action2Visitor<CircusCommunicationList>,
  //SeqActionVisitor,                                       C.12.12
  //InterruptActionVisitor,
  //ExtChoiceActionVisitor,                                 C.12.13
  //IntChoiceActionVisitor,                                 C.12.14  
  InterleaveActionVisitor<CircusCommunicationList>,             //  C.12.15, C.12.16
  ParallelActionVisitor<CircusCommunicationList>,               //  C.12.17
  AlphabetisedParallelActionVisitor<CircusCommunicationList>,   //  C.12.17-2
  HideActionVisitor<CircusCommunicationList>,                   //  C.12.18
  RenameActionVisitor<CircusCommunicationList>,                 //  NEW
  MuActionVisitor<CircusCommunicationList>,                     //  C.12.21
  ActionIteVisitor<CircusCommunicationList>,                      
  //SeqActionIteVisitor,                                    C.12.22
  //ExtChoiceActionIteVisitor,                              C.12.23
  //IntChoiceActionIteVisitor,                              C.12.24  
  ParActionIteVisitor<CircusCommunicationList>,                 //  C.12.25, C.12.26
  ParallelActionIteVisitor<CircusCommunicationList>,            //  C.12.27
  AlphabetisedParallelActionIteVisitor<CircusCommunicationList>//  C.12.27-2

  /* Support for Circus Time (hack F Zeyda) */
//  TimeoutActionVisitor<CircusCommunicationList>,
//  WaitActionVisitor<CircusCommunicationList>,
//  DeadlineActionVisitor<CircusCommunicationList>
  
{
  private final Expr arithmos_;
  
  /** Creates a new instance of ActionChecker */
  public ActionChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    setCurrentActionSignature(null);
    arithmos_ = factory().createRefExpr(factory().createZDeclName(ZString.ARITHMOS));
    
  }
  
  private ActionSignature actionSignature_;  
  
  protected ActionSignature getCurrentActionSignature()
  {    
    checkActionSignature(null); 
    return actionSignature_;
  }
  
  protected ActionSignature setCurrentActionSignature(ActionSignature sig)
  {
    ActionSignature old = actionSignature_;      
    actionSignature_ = sig;
    return old;
  }
  
  protected void checkActionSignature(Object term)
  {
    assert actionSignature_ != null : "null action signature whilst visiting " + (term != null ? term.getClass().getSimpleName() : "null");
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
  protected CircusCommunicationList typeCheckActionD(ActionD term, 
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
    CircusCommunicationList commList = visit(action);
    
    // if nesting is present, raise an error - it isn't allowed
    // unless we have a call action or is call action, in which case 
    // parameters may be present. Otherwise, if a MuAction, it must not
    // contain parameters itself
    boolean formalsAreBadlyFormed = 
       (!(action instanceof CallAction) &&
       !actionSignature_.getFormalParams().getNameTypePair().isEmpty())
       ||    
       ((action instanceof MuAction) && ((MuAction)action).isParameterised())        
       ;
    if (formalsAreBadlyFormed)
    {
      Object[] params = { getCurrentProcessName(), getCurrentActionName() };
      error(term, ErrorMessage.NESTED_FORMAL_PARAMS_IN_ACTION, params);
    }   
    // updates the formal parameters signature with gParams     
    actionSignature_.setFormalParams(factory().createSignature(gParams));    
        
    // updates the local variable signature with allVars - duplicates are fine; they represent scoping
    actionSignature_.getLocalVars().getNameTypePair().addAll(0, allVars);
    
    // add all communications.
    //GlobalDefs.addAllNoDuplicates(commList, actionSignature_.getUsedCommunications());    
    
    typeEnv().exitScope();            
    
    return commList;
  }  
  
  /**
   * Typechecks all iterated actions. It performs the general protocol for
   * actions with declaring parameters (ActionD), and then make sure the 
   * types within the declarations are finite.
   * @param term
   * @return
   */
  protected CircusCommunicationList typeCheckActionIte(ActionIte term)
  {    
    // all ActionIte are typechecked just liked ActionD
    // no qualified declaration is allowed - only param commands have them
    // and types of declarations ought to be finite
    CircusCommunicationList commList = typeCheckActionD(term, 
      true, /* considerFiniteness */
      false /* allowQualifiedDecl */);
    
    // iterated actions do not have parameters
    actionSignature_.getFormalParams().getNameTypePair().clear();
    return commList;
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

  protected void typeCheckTimeExpr(Term term, Expr expr)
  {
    // whatever the type, even if with generic, it must be at least ARITHMOS
    // this include both \nat and \real for the time of TIME.
    Type2 found = GlobalDefs.unwrapType(expr.accept(exprChecker()));
    Type2 expected = arithmos_.accept(exprChecker());
    if (expected instanceof PowerType)
    {
      expected = ((PowerType)expected).getType();
    }
    // if arithmos type is wrong somehow, this will catch it.
    // DON'T CACHE arithmos type as it won't work from the beginning.
    if (!unify(found, expected).equals(UResult.SUCC))
    {
      Object[] params = {
        getCurrentProcessName(), getCurrentActionName(),
        term.getClass().getSimpleName(), expr, expected, found
      };
      error(term, ErrorMessage.CIRCUS_TIME_EXPR_DONT_UNIFY, params);
    }
  }
  
  protected CircusCommunicationList typeCheckParActionIte(ParActionIte term, ChannelSet cs)
  {
    // type check name set and channel set
    NameSet ns = term.getNameSet();
    typeCheckNameSet(ns, getNameSetErrorParams());
    
    // null for interleaving
    if (cs != null)
    {
      @SuppressWarnings("unused")
	ChannelSetType cst = typeCheckChannelSet(cs, getChannelSetErrorParams());        
    }
    
    // typecheck inner action
    CircusCommunicationList commList = typeCheckActionIte(term);    
    
    GlobalDefs.addNoDuplicates(0, ns, actionSignature_.getUsedNameSets());
    
    // null for interleaving
    if (cs != null)
    {
      GlobalDefs.addNoDuplicates(0, cs, actionSignature_.getUsedChannelSets());      
    }
    
    return commList;
  }
  
  protected CircusCommunicationList typeCheckParAction(ParAction term, List<ChannelSet> channelSets)
  {
    checkActionParaScope(term, null);
    
    // check the name sets
    NameSet nsL = term.getLeftNameSet();
    NameSet nsR = term.getRightNameSet();  
    List<Object> errorParams = getNameSetErrorParams();
    typeCheckNameSet(nsL, errorParams);
    typeCheckNameSet(nsR, errorParams);
    
    // typecheck inner actions
    CircusCommunicationList commList = visitAction2(term);
        
    // update name sets used - L first; R next
    // i.e., add the last one first at the head then the next, gives this order    
    GlobalDefs.addNoDuplicates(0, nsR, actionSignature_.getUsedNameSets());
    GlobalDefs.addNoDuplicates(0, nsL, actionSignature_.getUsedNameSets());
       
    
    // within the ActionChecker, it must be for an action use 
    // rather than at declaration point.
    errorParams = getChannelSetErrorParams();
    
    // check the channel sets
    for(ListIterator<ChannelSet> lit = 
        channelSets.listIterator(channelSets.size()); 
        lit.hasPrevious() ; ) 
    {
      ChannelSet cs = lit.previous();
      @SuppressWarnings("unused")
	ChannelSetType cst = typeCheckChannelSet(cs, errorParams);      
      GlobalDefs.addNoDuplicates(0, cs, actionSignature_.getUsedChannelSets());      
    }    
        
    return commList;
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
  public CircusCommunicationList visitParamAction(ParamAction term)
  {     
    // commands allow qualified declarations    
    // and types of declarations do not need to be finite
    CircusCommunicationList commList = typeCheckActionD(term, 
      false,                /* considerFiniteness */
      term.isParamCommand() /* allowQualifiedDecl */);    
    return commList;
  }
  
  /**
   * Returns an empty action signature. It covers Skip, Stop, and Chaos.
   *
   *@law C.12.3
   */
  @Override
  public CircusCommunicationList visitSchExprAction(SchExprAction term)
  {
    // Action ::= Schema-Exp    
    checkActionParaScope(term, null);

    // type check the schema expressions    
    Type type = term.getExpr().accept(exprChecker());
    
    // create an empty signature
    CircusCommunicationList commList = factory().createEmptyCircusCommunicationList();

    SchemaType schType = referenceToSchema(type);
    if (schType != null)
    {  
      // checks the schema expression adding local variables to the signature.
      List<ErrorAnn> varScopeErrors = checkStateVarsScopeInSchExprAction(term, schType);
      
      // if no errors were found, add local vars to the signature
      if (varScopeErrors.isEmpty())
      {        
        actionSignature_.getLocalVars().getNameTypePair().addAll(schType.getSignature().getNameTypePair());
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
        
    warningManager().warn("Schema expression action still requires StateUpdate in process signature." +
      "\n\tProcess...: {0}\n\tAction....: {1}", getCurrentProcessName(), getCurrentActionName());    

    return commList;
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
  public CircusCommunicationList visitCallAction(CallAction term)
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
        addTermForPostChecking(term);
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
        addTermForPostChecking(term);
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
    
    CircusCommunicationList commList = factory().createEmptyCircusCommunicationList();
        
    // if action type, then clone the call signature
    if (type instanceof ActionType)
    {
      ActionSignature aSig = GlobalDefs.actionType(type).getActionSignature();
      commList.addAll(0, factory().deepCloneTerm(aSig.getUsedCommunications()));
    }
    // otherwise, see if this is a call for SchExpr action without special brackets, 
    // but only if no errors were found by the consistency method
    else if (callErrors.isEmpty())
    {      
      SchemaType schType = referenceToSchema(type);
      if (schType != null)
      {
        actionSignature_.getLocalVars().getNameTypePair().addAll(schType.getSignature().getNameTypePair());
      }      
    }        
   
    return commList;
  }

  /**
   * Forward command checking to the appropriate checker. This links C.12 with C.17.
   *
   *@law C.12.5
   */
  @Override
  public CircusCommunicationList visitCircusCommand(CircusCommand term)
  {
    return term.accept(commandChecker());
  }

  /**
   * Returns an empty action signature. It covers Skip, Stop, and Chaos.
   *
   *@law C.12.6, C.12.7, C.12.8
   */
  // Action ::= Skip | Stop | Chaos
  public CircusCommunicationList visitBasicAction(BasicAction term)
  {
    checkActionParaScope(term, null);
    return factory().createEmptyCircusCommunicationList();    
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
  public CircusCommunicationList visitSubstitutionAction(SubstitutionAction term)
  { 
    checkActionParaScope(term, null);

    // the parser enforces              #ln1 = #ln2
    ZRenameList zrl = term.getZRenameList();
    int i = 1;
    SubstResolution resolution;
    //boolean hasError = false;
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
          case Go:
        	name = "??? shouldn't be this value Go??? ";
        	break;
        }
        Object[] params = { getCurrentProcessName(), getCurrentActionName(), name, i, resolution };
        error(term, ErrorMessage.NOT_LOCAL_VAR_NAME_IN_SUBST_ACTION, params);
      }
      i++;
    }

    // check the action to substitute,  \Gamma \rhd a: Action
    CircusCommunicationList commList = visit(term.getCircusAction());
    return commList;
  }

  /**
   * Returns an action signature containing the list  . It covers Skip, Stop, and Chaos.
   *@law C.12.10
   */
  // Action ::= Communication -> Action  
  public CircusCommunicationList visitPrefixingAction(PrefixingAction term)
  {
    checkActionParaScope(term, null);

    // enter the scope for input fields
    typeEnv().enterScope();

    // typecheck the communication part returning a list of name type pairs
    // it returns the input variables that need to be declared.
    // * calculate (VarsC c \Gamma)
    Communication comm = term.getCommunication();
    List<NameTypePair> comSig = comm.accept(commChecker());
    List<NameTypePair> inputVars = ((CommunicationChecker) commChecker()).filterInputs(comSig);

    // Adds input variables into S1. The oplus at the signature level is implemented down below.
    // * create \Gamma' = (\Gamma \oplus (VarsC c \Gamma)) 
    // 
    // NOTE: variables should be added locally at the input field 
    //addStateVars(inputVars, ? pos ?);

    // type check given action in scope enriched with input variables
    // * checks \Gamma' \rhd a : Action
    CircusCommunicationList commList = visit(term.getCircusAction());

    // updates the local variable signature for the prefixed action.
    actionSignature_.getLocalVars().getNameTypePair().addAll(inputVars);
    
    // add the channels used channels
    GlobalDefs.addNoDuplicates(0, commChecker().lastUsedChannelDecl(), 
      actionSignature_.getUsedChannels().getNameTypePair());
      
    // add the communication expressions!    
    //GlobalDefs.addNoDuplicates(0, comm, actionSignature_.getUsedCommunications());
    GlobalDefs.addNoDuplicates(0, comm, commList);

    // close input variables scope after analysing the entailing action
    typeEnv().exitScope();
    
    return commList;
  }

  /**
   * First checks the predicate in the guard, where possible partial evaluation
   * is considered, and then checkes the guarded action itself.
   * 
   *@law C.12.11
   */
  // Action ::= Predicate & Action  
  @Override
  public CircusCommunicationList visitGuardedAction(GuardedAction term)
  {
    checkActionParaScope(term, null);    
    typeCheckPred(term, term.getPred());
    CircusCommunicationList commList = visit(term.getCircusAction());
    return commList;
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
  public CircusCommunicationList visitAction2(Action2 term)
  {
    // check within an action paragraph scope.
    checkActionParaScope(term, null);

    // check each side
    CircusCommunicationList commListL = visit(term.getLeftAction());
    CircusCommunicationList commListR = visit(term.getRightAction());
    
    CircusCommunicationList result = factory().createCircusCommunicationList(commListR);
    GlobalDefs.addAllNoDuplicates(0, commListL, result);    

    return result;
  }

  /**
   * Partial.
   *@law C.12.16
   */
  public CircusCommunicationList visitInterleaveAction(InterleaveAction term)
  {
    CircusCommunicationList commList = typeCheckParAction(term, factory().<ChannelSet>list());        
    return commList;
  }

  /**   
   *@law C.12.17
   */
  public CircusCommunicationList visitParallelAction(ParallelAction term)
  {    
    CircusCommunicationList commList = typeCheckParAction(term, factory().<ChannelSet>list(term.getChannelSet()));    
    return commList;   
  }
  
  public CircusCommunicationList visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
  {
    CircusCommunicationList commList = typeCheckParAction(term, factory().<ChannelSet>list(
      term.getLeftAlpha(), term.getRightAlpha()));    
    return commList;  
  }

  /**
   * Typechecks the channel set and the inner action, checking both action and
   * process scopes. Creates and returns a signature containing the used 
   * channel set.
   *
   *@law C.12.18
   */
  public CircusCommunicationList visitHideAction(HideAction term)
  {
    // check within an action paragraph scope.
    checkActionParaScope(term, null);

    ChannelSet cs = term.getChannelSet();
    @SuppressWarnings("unused")
	ChannelSetType csType = typeCheckChannelSet(cs, getChannelSetErrorParams());

    // check the action itself and add signature
    CircusCommunicationList commList = visit(term.getCircusAction());
    
    // update name sets used    
    GlobalDefs.addNoDuplicates(0, cs, actionSignature_.getUsedChannelSets()); 
    
    return commList;
  }
  
  /**
   * 
   * @param term 
   * @return 
   * @law NEW
   */
  public CircusCommunicationList visitRenameAction(RenameAction term)
  {    
    checkActionParaScope(term, null);

    // first type check the process - it might add implicitly generic channels to the current process scope.
    CircusCommunicationList commList = term.getCircusAction().accept(actionChecker());
    
    typeCheckRenameListAssignmentPairs(term, commList);
    
    return commList;
  }

  /**
   * Puts the mu action name into scope with an empty action signature;
   * then make sure the action declaration 
   *
   *@law C.12.21
   */
  public CircusCommunicationList visitMuAction(MuAction term)
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
    
    // if it is a parameterised Mu action, we also need to add the 
    // parameters to the signature, so that calls will be parameterised
    //
    // NOTE: this is not in the original type rules - asked to be added by Ana, 13/04/08
    if (term.isParameterised())
    {
      ParamAction paramAction = (ParamAction)term.getCircusAction();
      // just like in typeCheckActionD, but only the parameters please
      List<NameTypePair> gParams = typeCheckCircusDeclList(
        paramAction, paramAction.getZDeclList(), 
        false                        /* considerFiniteness - just like as in visitParamAction */,
        paramAction.isParamCommand() /* allowQualifiedDecl - just like as in visitParamAction */, 
        ErrorMessage.INVALID_DECL_IN_ACTIONITE, 
        factory().<Object>list(getCurrentProcessName(), getCurrentActionName()));
      
      // again, just like typeCheckActionD, update the signature formal parameters
      // so that Mu calls will work nicely within the Mu aSig
      aSig.setFormalParams(factory().createSignature(gParams));            
    }    
    ActionType aType = factory().createActionType(aSig);    
    NameTypePair recVarPair = factory().createNameTypePair(aName, aType);    
    typeEnv().add(recVarPair);
    
    // this action signature is set into "action" through the addActionSignatureAnn
    // method present in all other visitors. So, "action" already have the signature
    // annotation with "aName" associated with it.
    ActionSignature actionSignature = checkActionDecl(aName, action, term);
    
    // exit recursive variable scope
    typeEnv().exitScope();
    
    // update the action type for the call action
    aType.setActionSignature(actionSignature);
    
    // add action type to CircusAction 
    addTypeAnn(term, aType);
         
    CircusCommunicationList commList = factory().createCircusCommunicationList(actionSignature.getUsedCommunications());    
    return commList;    
  }
  
/**
   * 
   * @param term
   * @return
   * 
   * @law C.12.22, C.12.23, C.12.24
   */
  public CircusCommunicationList visitActionIte(ActionIte term)
  {    
    CircusCommunicationList commList = typeCheckActionIte(term);    
    return commList;    
  }
  
  /**
   * Interleaving 
   * @param term
   * @return
   * 
   * * @law C.12.25, C.12.26
   */
  public CircusCommunicationList visitParActionIte(ParActionIte term)
  {     
    CircusCommunicationList commList = typeCheckParActionIte(term, null);        
    return commList;    
  }

  /**
   * 
   * @param term
   * @return
   * 
   * @law C.12.27
   */   
  public CircusCommunicationList visitParallelActionIte(ParallelActionIte term)
  { 
    CircusCommunicationList commList = typeCheckParActionIte(term, term.getChannelSet());    
    return commList;
  }
  
  /**
   * 
   * @param term
   * @return
   * 
   * @law C.12.27-2
   */   
  public CircusCommunicationList visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
  {
    CircusCommunicationList commList = typeCheckParActionIte(term, term.getChannelSet());    
    return commList;
  }

  /* Support for Circus Time (hack F Zeyda) */
//  @Override
//  public CircusCommunicationList visitTimeoutAction(TimeoutAction term)
//  {
//    CircusCommunicationList commList = visitAction2(term);
//    typeCheckTimeExpr(term, term.getExpr());
//    return commList;
//  }
//
//  @Override
//  public CircusCommunicationList visitWaitAction(WaitAction term)
//  {
//    CircusCommunicationList commList = visitBasicAction(term);
//    typeCheckTimeExpr(term, term.getExpr());
//    return commList;
//  }
//
//  @Override
//  public CircusCommunicationList visitDeadlineAction(DeadlineAction term)
//  {
//    checkActionParaScope(term, null);
//    CircusCommunicationList commList = visit(term.getCircusAction());
//    typeCheckTimeExpr(term, term.getExpr());
//    return commList;
//  }
}
