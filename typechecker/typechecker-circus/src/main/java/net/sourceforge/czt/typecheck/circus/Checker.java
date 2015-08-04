/*
Copyright (C) 2005, 2006, 2007, 2008 Leo Freitas
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

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionSignatureAnn;
import net.sourceforge.czt.circus.ast.ActionSignatureList;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.AssignmentPairs;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.ast.ChannelSet;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.CircusType;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.NameSet;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessSignatureAnn;
import net.sourceforge.czt.circus.ast.ProcessSignatureList;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.ChannelSetList;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.CommunicationList;
import net.sourceforge.czt.circus.ast.NameSetList;
import net.sourceforge.czt.circus.ast.QualifiedDecl;
import net.sourceforge.czt.circus.ast.RenameAction;
import net.sourceforge.czt.circus.ast.RenameProcess;
import net.sourceforge.czt.circus.ast.SignatureList;
import net.sourceforge.czt.circus.ast.StateUpdate;
import net.sourceforge.czt.circus.ast.ZSignatureList;
import net.sourceforge.czt.circus.util.CircusConcreteSyntaxSymbol;
import net.sourceforge.czt.circus.util.CircusConcreteSyntaxSymbolVisitor;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.parser.util.ErrorType;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.impl.VariableSignature;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.UndeterminedTypeException;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.util.ZString;

/**
 * Derived superclass of all XXXChecker classes (i.e., one for each syntactic 
 * category). It provides general facilities for the derived checkers. This 
 * usually includes typeing environment lookup and update, factory methods,
 * syntax checks, and so on.
 *
 * @param R 
 * @author Leo Freitas
 */
public abstract class Checker<R>
  extends net.sourceforge.czt.typecheck.z.Checker<R>
{

  /**
   * As mu actions could be parameterised, but only when at the beginning of
   * a action paragraph, we keep a count over it to make sure inner parameterised
   * mu actions are not allowed. This doesn't happen with ParamAction because the
   * parser does not allow it; but the same is not the case for MuActions, which 
   * when without parameters, can appear anywhere. The count is reset at visitActionPara
   * and incremented at each term.accept(actionChecker), which is centralised in the
   * #visit(CircusAction) method below.
   */
  private int actionCheckerVisitCount_;

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    assert typeChecker != null;
    typeChecker_ = typeChecker;
    resetActionCheckerVisitCount();
  }
  
  /**
   * Overrides the default Z protocol to use the warning manager
   * @param term
   * @return
   */
  public R visitTerm(Term term)
  {    
    warningManager().warn(term, WarningMessage.UNKNOWN_TERM, 
      this.getClass().getName(), 
      getConcreteSyntaxSymbol(term));    
    return null;
  }

  protected final void resetActionCheckerVisitCount()
  {
    actionCheckerVisitCount_ = 0;
  }

  // cast the underlying Z typeChecker_ protected object into a Circus typechecked object
  protected TypeChecker getCircusTypeChecker()
  {
    return (TypeChecker)typeChecker_;
  }
  
  /**
   * Gives access to the typechecking factory for all checkers. 
   * 
   * @return typechecking factory that takes variable types/signature into account.
   */
  protected net.sourceforge.czt.typecheck.circus.impl.Factory factory()
  {
    return getCircusTypeChecker().getFactory();
  }

  /**
   * Let var terms are important for proof obligation generators that require 
   * scoping information of local variables with their declared, rather than 
   * maximal, types.
   * @return determines if the typechecker should create let var terms or not.
   */
  protected boolean shouldCreateLetVar()
  {
    return getCircusTypeChecker().shouldCreateLetVars_;
  }

  /**
   * Let mu terms are important  for mutually recursive processes and actions.
   * @return determines if the typechecker should create let mu terms or not.
   */
  protected boolean shouldCreateLetMu()
  {
    return getCircusTypeChecker().shouldCreateLetMu_;
  }

  /***********************************************************************
   * Checker accessors per syntactic category
   **********************************************************************/
  protected ProcessChecker processChecker()
  {
    return getCircusTypeChecker().processChecker_;
  }

  protected Checker<Signature> processParaChecker()
  {
    return getCircusTypeChecker().processParaChecker_;
  }

  protected BasicProcessChecker basicProcessChecker()
  {
    return getCircusTypeChecker().basicProcessChecker_;
  }
  
  protected ActionChecker actionChecker()
  {
    return getCircusTypeChecker().actionChecker_;
  }

  protected Checker<List<NameTypePair>> commChecker()
  {
    return getCircusTypeChecker().commChecker_;
  }

  protected Checker<CircusCommunicationList> commandChecker()
  {
    return getCircusTypeChecker().commandChecker_;
  }

  protected CircusConcreteSyntaxSymbolVisitor concreteSyntaxSymbolVisitor()
  {
    return getCircusTypeChecker().concreteSyntaxSymbolVisitor_;
  }

  protected WarningManager warningManager()
  {
    return getCircusTypeChecker().warningManager_;
  }
  
  @Override
  protected void setMarkup(Markup markup)
  {
    super.setMarkup(markup);
    warningManager().setMarkup(markup);
  }
  
  @Override
  protected void setSectName(String sectName)
  {
    super.setSectName(sectName);
    warningManager().setCurrentSectName(sectName);
  }
  
  // TODO
  protected Checker<Signature> signatureChecker()
  {
    return getCircusTypeChecker().signatureChecker_;
  }  
//  protected Checker<Boolean> channelDeclChecker()
//  {
//    return typeChecker_.channelDeclChecker_;
//  }
//  
//  protected Checker<NameList> channelsUsedChecker()
//  {
//    return typeChecker_.channelsUsedChecker_;
//  }

//  /** 
//   * General method that checks whether the given name is typed with
//   * the expected type Type class. If the type info stack does not have
//   * type information for the given name, the result is obviously false
//   * regardless of the expected class.
//   */
//  protected boolean isTypedAsExpected(Name name, Class<? extends Type> expected)
//  {
//    assert name != null && expected != null;
//    
//    // NOTE: Originally, Manuela used name comparison (possibly) without 
//    //       considering strokes (see GlobalDefs.compareNames). This does
//    //       not seem to make much sense and it wasn't well motivated. 
//    //       In any case, TypeEnv.getType uses getX, which uses "namesEqual"
//    //       method that does the right name comparison.
//    
//    // retrieve type information for given name
//    Type type = getType(name);        
//    
//    // checks whether it is non-null and of the expected type    
//    return expected.isInstance(type);
//  }
//  
//   /** A name is a nameset if it has NameSetType */
//  public boolean isChannel(Name name)
//  {    
//    return isTypedAsExpected(name, ChannelType.class);
//  }
//  
//  /** A name is a nameset if it has NameSetType */
//  public boolean isNameSet(Name name)
//  {    
//    return isTypedAsExpected(name, NameSetType.class);
//  }
//  
//  /** A name is an action if it has ProcessType */
//  public boolean isProcess(Name name)
//  {
//    return isTypedAsExpected(name, ProcessType.class);    
//  }
//  
//  /** A name is an action if it has ActionType */
//  public boolean isAction(Name name)
//  {
//    return isTypedAsExpected(name, ActionType.class);    
//  }  
//  /**
//   * A name is a parameterised action if it has ActionType
//   * and the formal parameters signature within the action 
//   * signature is not empty.
//   */
//  public boolean isParamAction(Name name) 
//  {    
//    Type type = getType(name);
//    boolean result = isAction(name);
//    if (result)
//    {      
//      ActionType atype = (ActionType)type;
//      result = !atype.getActionSignature().getFormalParams().getNameTypePair().isEmpty();
//    }    
//    return result;
//  }
  /***********************************************************************
   * Accessor methods to the various syntactic categories lists
   **********************************************************************/
  /*
  protected List<ChannelInfo> channels()
  {
  return typeChecker_.channels_;
  }
  protected NameList chansets()
  {
  return typeChecker_.chansets_;
  }
  protected NameList muProcesses()
  {
  return typeChecker_.muProcesses_;
  }
  protected NameList muActions()
  {
  return typeChecker_.muActions_;
  }
  protected NameList actions4PostCheck()
  {
  return typeChecker_.actions4PostCheck_;
  }  
   */
  /***********************************************************************
   * Methods for the various process related information 
   **********************************************************************/
  protected Name getCurrentProcessName()
  {
    return getCircusTypeChecker().currentProcessName_;
  }

  protected ZName getCurrentProcessZName()
  {
    return ZUtils.assertZName(getCurrentProcessName());
  }

  protected Name setCurrentProcessName(Name name)
  {
    Name old = getCircusTypeChecker().currentProcessName_;
    getCircusTypeChecker().currentProcessName_ = name;
    return old;
  }

  protected CircusProcess getCurrentProcess()
  {
    return getCircusTypeChecker().currentProcess_;
  }
  
  protected BasicProcess getCurrentBasicProcess()
  {
    CircusProcess result = getCurrentProcess();    
    return (CircusUtils.isBasicProcess(result) ? CircusUtils.getBasicProcess(result) : null);
  }

  protected CircusProcess setCurrentProcess(CircusProcess process)
  {
    CircusProcess old = getCircusTypeChecker().currentProcess_;
    getCircusTypeChecker().currentProcess_ = process;
    return old;
  }
  
  protected Name getCurrentChannelSetName()
  {
    return getCircusTypeChecker().currentChannelSetName_;
  }

  protected ZName getCurrentChannelSetZName()
  {
    return ZUtils.assertZName(getCurrentChannelSetName());
  }

  protected Name setCurrentChannelSetName(Name name)
  {
    Name old = getCircusTypeChecker().currentChannelSetName_;
    getCircusTypeChecker().currentChannelSetName_ = name;
    return old;
  }
  
  protected ChannelSet getCurrentChannelSet()
  {
    return getCircusTypeChecker().currentChannelSet_;
  }

  protected ChannelSet setCurrentChannelSet(ChannelSet channelSet)
  {
    ChannelSet old = getCircusTypeChecker().currentChannelSet_;
    getCircusTypeChecker().currentChannelSet_ = channelSet;
    return old;
  }
  
  /**
   * This flag must be set whenever we are performing typechecking 
   * over circus formal paramters. This is important to make sure 
   * only VarDecl or QualifiedDecl is allowed.
   */
  protected void setCircusFormalParametersDecl(boolean params, boolean qualified)
  {
    getCircusTypeChecker().circusFormalParameters_ = params;
    getCircusTypeChecker().circusQualifiedParams_  = qualified;
  }

  protected boolean isCheckingCircusFormalParamDecl()
  {
    return getCircusTypeChecker().circusFormalParameters_;
  }
  
  protected boolean isQualifiedParamAllowed()
  {
    return getCircusTypeChecker().circusQualifiedParams_;
  }
  
  protected void setCheckingStatePara(boolean flag)
  {
    getCircusTypeChecker().isCheckingStatePara_ = (flag && getCurrentBasicProcess() != null);
  }
  
  protected boolean isCheckingStatePara()
  {
    return getCircusTypeChecker().isCheckingStatePara_;
  }
  /**
   * Return whether the typechecker is within the scope of a process paragraph.
   * This is useful to check whether a process declaration can be analysed, or
   * to avoid nested scopes. The latter is already enforced by the parser.   
   */
  protected boolean isWithinProcessParaScope()
  {
    return getCircusTypeChecker().currentProcessName_ != null &&
      getCircusTypeChecker().currentProcess_ != null;
  }
  
  protected boolean isWithinChannelSetParaScope()
  {
    return (getCircusTypeChecker().currentChannelSetName_ != null &&
      getCircusTypeChecker().currentChannelSet_ != null);
  }

  protected boolean checkProcessParaScope(Term term, Name name)
  {
    processChecker().checkProcessSignature(term);
    boolean result = isWithinProcessParaScope();
    if (!result)
    {
      List<Object> params = factory().list();      
      params.add(getConcreteSyntaxSymbol(term));
      params.add(name != null ? name : "???");
      error(term, ErrorMessage.INVALID_PROCESS_PARA_SCOPE, params);
    }
    return result;
  }  
  
  protected boolean checkChannelSetScope(Term term)
  {
    // when used
    boolean inProcessPara = isWithinProcessParaScope();        
    boolean inActionPara  = isWithinActionParaScope();
    // when declared
    boolean inChannelSetPara = isWithinChannelSetParaScope();    
    boolean result = (inProcessPara || inChannelSetPara || inActionPara);
    if (!result)
    {
      List<Object> params = factory().list();            
      params.add((inProcessPara ? "process" : (inActionPara ? "action" : 
        (inChannelSetPara ? "channel set" : "???"))));
      params.add((inActionPara ? 
        (getCurrentProcessName().toString() + "\n\tAction...:" +
         getCurrentActionName().toString()) :
        (inProcessPara ? getCurrentProcessName() :
            (inChannelSetPara ? getCurrentChannelSetName() : "error"))));
      params.add(getConcreteSyntaxSymbol(term));      
      error(term, ErrorMessage.INVALID_CHANNELSET_SCOPE, params);      
    }
    return result;
  }
  
  protected CircusConcreteSyntaxSymbol getConcreteSyntaxSymbol(Term term)
  {
    return term.accept(concreteSyntaxSymbolVisitor());
  }

  /***********************************************************************
   * Methods for the on-the-fly process related information 
   **********************************************************************/
  protected void setOnTheFlyProcesses(ZParaList procs)
  {
    getCircusTypeChecker().onTheFlyProcesses_ = procs;
  }

  protected ZParaList onTheFlyProcesses()
  {
    return getCircusTypeChecker().onTheFlyProcesses_;
  }

  /***********************************************************************
   * Methods for the various action related information 
   **********************************************************************/
  protected Name getCurrentActionName()
  {
    return getCircusTypeChecker().currentActionName_;
  }

  protected ZName getCurrentActionZName()
  {
    return ZUtils.assertZName(getCurrentActionName());
  }

  protected Name setCurrentActionName(Name name)
  {
    Name old = getCircusTypeChecker().currentActionName_;
    getCircusTypeChecker().currentActionName_ = name;
    return old;
  }

  protected CircusAction getCurrentAction()
  {
    return getCircusTypeChecker().currentAction_;
  }

  protected CircusAction setCurrentAction(CircusAction action)
  {
    CircusAction old = getCircusTypeChecker().currentAction_;
    getCircusTypeChecker().currentAction_ = action;
    return old;
  }
  
  protected Name getCurrentNameSetName()
  {
    return getCircusTypeChecker().currentNameSetName_;
  }

  protected ZName getCurrentNameSetZName()
  {
    return ZUtils.assertZName(getCurrentNameSetName());
  }

  protected Name setCurrentNameSetName(Name name)
  {
    Name old = getCircusTypeChecker().currentNameSetName_;
    getCircusTypeChecker().currentNameSetName_ = name;
    return old;
  }
  
  protected NameSet getCurrentNameSet()
  {
    return getCircusTypeChecker().currentNameSet_;
  }

  protected NameSet setCurrentNameSet(NameSet nameSet)
  {
    NameSet old = getCircusTypeChecker().currentNameSet_;
    getCircusTypeChecker().currentNameSet_ = nameSet;
    return old;
  }
  
  /**
   * 
   * @return
   */
  protected List<? extends Para> getCurrentOnTheFlyActions()
  {
    BasicProcess bp = getCurrentBasicProcess();
    return (bp != null ? bp.getOnTheFlyPara() : null);
  }

  /**
   * Return whether the typechecker is within the scope of an action paragraph.
   * That means, the action declaration is within an action paragraph, which in
   * turn must be within a process paragraph.
   * This is useful to check whether a action declaration can be analysed, or
   * to avoid nested scopes. The latter is already enforced by the parser.   
   */
  protected boolean isWithinActionParaScope()
  {
    return (isWithinProcessParaScope() &&
      getCircusTypeChecker().currentActionName_ != null &&
      getCircusTypeChecker().currentAction_ != null);
  }  
  
  protected boolean isWithinNameSetParaScope()
  {
    return (isWithinProcessParaScope() &&
      getCircusTypeChecker().currentNameSetName_ != null &&
      getCircusTypeChecker().currentNameSet_ != null);
  }  

  protected boolean checkActionParaScope(Term term, Name name)
  {    
    actionChecker().checkActionSignature(term);
    boolean result = isWithinActionParaScope();
    if (!result)
    {
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add(getConcreteSyntaxSymbol(term));
      params.add(name != null ? name : "???");
      error(term, ErrorMessage.INVALID_ACTION_PARA_SCOPE, params);
    }
    return result;
  }
  
  /**
   * Checks whether the given name set is within either a NameSetPara or
   * action para scopes. That is, a name set can only appear at its 
   * declaration or when used in an action.
   * @param term
   */
  protected boolean checkNameSetScope(Term term)
  {
    boolean inActionPara = isWithinActionParaScope();
    boolean inNameSetPara = isWithinNameSetParaScope();    
    boolean result = (inActionPara || inNameSetPara);
    if (!result)
    {
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add((inActionPara ? "action" : (inNameSetPara ? "name set" : "???")));
      params.add((inActionPara ? getCurrentActionName() : 
        (inNameSetPara ? getCurrentNameSetName() : "error")));
      params.add(getConcreteSyntaxSymbol(term));      
      error(term, ErrorMessage.INVALID_NAMESET_SCOPE, params);      
    }
    return result;
  }

  /**
   * Checks that the given special type in the global SectTypeEnv is
   * the one expected. That means, it checks whether or not the global
   * environment for Circus has been properly initialised, since the 
   * type as it should be is present in (and retrieved from) CircusUtils.
   * Circus has two such types: synchronisation channel, and transformer paragraph.
   * 
   * @param name 
   * @param expected 
   * @return the type found if no exception is thrown.
   * @throws UndeterminedTypeException if SectTypeEnv is not properly initialised.
   */
  protected Type2 checkUnificationSpecialType(ZName name, Type2 expected)
  {
    assert name != null && expected != null;
    
    // just check the circus prelude is visible.? Only 
    assert sectTypeEnv().visibleSections().contains(CircusUtils.CIRCUS_PRELUDE) : 
      "Circus prelude not yet loaded in global type environment";
    
    Type2 found = GlobalDefs.unwrapType(sectTypeEnv().getType(name));
    
    assert !(found instanceof UnknownType) : "Special type " + name + 
      " must be known in the sect type environment before creating the checker.";
    
    UResult resolved = unify(expected, found);
    if (!resolved.equals(UResult.SUCC))
    {
      throw new UndeterminedTypeException("Could not unify special type " + name + 
        "with SectTypeEnv information.\n\tExpected: " + expected + "\n\tFound: " + found);
    }      
    return found;
  }
  
  /***********************************************************************
   * Methods for the basic process state related information 
   **********************************************************************/
  protected Name getStateName()
  {
    return getCircusTypeChecker().stateName_;
  }

  protected ZName getZStateName()
  {
    return ZUtils.assertZName(getStateName());
  }

  protected void setStateName(Name name)
  {
    getCircusTypeChecker().stateName_ = name;
  }

  protected Type getLocalType(Name name)
  {
    return getLocalType(ZUtils.assertZName(name));
  }
  
  protected Type getLocalType(ZName name)
  {
    return typeEnv().getType(name);
  }
  
  protected Type getGlobalType(Name name)
  {
    return getGlobalType(ZUtils.assertZName(name));
  }
  
  protected Type getGlobalType(ZName name)
  {
    return getType(name);
  }
  
//  /**
//   * Overrides the old signature with type from pairs the new siganature
//   * with the same name. TODO: ask Tim about name ids business
//   */
//  protected Signature overrideSignature(Signature oldSig, Signature newSig)
//  {
//    Signature result = factory().createSignature();
//    List<NameTypePair> resultPairs = result.getNameTypePair();
//    resultPairs.addAll(oldSig.getNameTypePair());        
//    for(NameTypePair pair : newSig.getNameTypePair())
//    {      
//      GlobalDefs.namesEqual(pair.getName(), )
//      pair.getZName().setId(null)
//      if(!resultPairs.contains(pair))
//      {
//        resultPairs.add(pair);
//      }
//    }
//    return result;
//  }
  /**
   * Given the channel decl term, and the result of unifying the underlying 
   * type with the (possibly) generically instantiated power type it corresponds
   * to, creates the list of Name type pairs for that channel declaration. 
   * (see createDeclNames in z.Checker).
   */
  protected List<NameTypePair> checkChannelDecl(List<? extends Name> declNames,
    Expr channelExpr, UResult unified, Type2 exprType, PowerType vType)
  {
    // check each name corresponds to a power type
    List<NameTypePair> result = checkDeclNames(declNames,
      channelExpr, unified, exprType, vType);

    // wrap up the result base type as a channel type or generic channel type
    // depending on the current value of typeEnv().getParameters().size(). see #addGenerics
    for (NameTypePair pair : result)
    {      
      Type2 type = GlobalDefs.unwrapType(pair.getType());
      ChannelType cType = factory().createChannelType(type);
      Type gType = addGenerics(cType);
      pair.setType(gType);
      // add channel type annotation to channel name
      addTypeAnn(pair.getName(), gType);
      
      // add it to the pending environment
      pending().add(pair);
    }
    return result;
  }
  
  @Override
  protected Type2 instantiate(Type2 type)
  {
    Type2 result = factory().createUnknownType();
    if (type instanceof ChannelType)      
    {
      ChannelType chanType = (ChannelType) type;
      Type2 replaced = instantiate(chanType.getType());
      result = factory().createChannelType(replaced);
    }
    else if (type instanceof CommunicationType)
    {
      CommunicationType commType = (CommunicationType) type;
      Signature signature = instantiate(commType.getSignature());
      result = factory().createCommunicationType(signature);
    }
    else if (type instanceof ChannelSetType)
    {
      ChannelSetType csType = (ChannelSetType) type;
      Signature signature = instantiate(csType.getSignature());
      result = factory().createChannelSetType(signature);
    }
    else if (type instanceof ProcessType)
    {
      ProcessType pType = (ProcessType) type;      
      ProcessSignature procSig = instantiate(pType.getProcessSignature());      
      result = factory().createProcessType(procSig);
    }
    else if (type instanceof ActionType)
    {
      ActionType aType = (ActionType) type;
      ActionSignature actionSig = instantiate(aType.getActionSignature());      
      result = factory().createActionType(actionSig);
    }
    else if (type instanceof NameSetType)
    {
      NameSetType nsType = (NameSetType) type;
      Signature signature = instantiate(nsType.getSignature());
      result = factory().createNameSetType(signature);
    }
    // otherwise, look for Z types.
    else
    {
      result = super.instantiate(type);
    }
    return result;
  }
  
  protected ActionSignature instantiate(ActionSignature signature)
  {
    Signature instFormals = instantiate(signature.getFormalParams());
    Signature instLocalVars = instantiate(signature.getLocalVars());
    // used channels are given as declared, so no instantiation is needed, hence just clone then
    Signature usedChannels = factory().deepCloneTerm(signature.getUsedChannels());
    CommunicationList instComms = instantiate(signature.getUsedCommunications());
    ChannelSetList instChannelSets = instantiate(signature.getUsedChannelSets());
    NameSetList instNameSets = instantiate(signature.getUsedNameSets());
    ActionSignature result = factory().createCompleteActionSignature(
      signature.getActionName(), instFormals, instLocalVars, usedChannels, 
      instComms, instChannelSets, instNameSets);
    return result;
  }
  
  protected CommunicationList instantiate(CommunicationList commList)
  {
    // communication lists are already isntantiated, so just clone then
    return factory().deepCloneTerm(commList);
  }
  
  protected ChannelSetList instantiate(ChannelSetList chanSetList)
  {
    // channel set lists are already isntantiated, so just clone then
    return factory().deepCloneTerm(chanSetList);
  }
  
  protected NameSetList instantiate(NameSetList nameSetList)
  {
    // name set lists are already isntantiated, so just clone then
    return factory().deepCloneTerm(nameSetList);
  }
  
  protected SignatureList instantiate(SignatureList sigList)
  {
    SignatureList result;
    if (sigList instanceof ZSignatureList)
    {
      ZSignatureList zSigList = (ZSignatureList)sigList;            
      ZSignatureList instZSigList = factory().getCircusFactory().createZSignatureList();
      for(Signature sig : zSigList)
      {
        Signature instZSig = instantiate(sig);
        instZSigList.add(instZSig);
      }
      result = instZSigList;
    }
    else if (sigList instanceof ActionSignatureList)
    {
      ActionSignatureList actionSigList = (ActionSignatureList)sigList;            
      ActionSignatureList instActionSigList = factory().getCircusFactory().createActionSignatureList();
      for(ActionSignature sig : actionSigList)
      {
        ActionSignature instActionSig = instantiate(sig);
        instActionSigList.add(instActionSig);
      }
      result = instActionSigList;
    }
    else if (sigList instanceof ProcessSignatureList)
    {
      ProcessSignatureList processSigList = (ProcessSignatureList)sigList;            
      ProcessSignatureList instProcessSigList = factory().getCircusFactory().createProcessSignatureList();
      for(ProcessSignature sig : processSigList)
      {
        ProcessSignature instProcessSig = instantiate(sig);
        instProcessSigList.add(instProcessSig);
      }
      result = instProcessSigList;
    }
    else
    {      
      throw new UnsupportedAstClassException("Unknown Circus signature list to instantiate generic types - " + sigList.getClass().getSimpleName());
    }
    return result;
  }
  
  protected List<? extends SignatureList> instantiate(List<? extends SignatureList> sigList)
  {
    List<SignatureList> result = factory().list();
    for(SignatureList sig : sigList)
    {
      SignatureList instSig = instantiate(sig);
      result.add(instSig);
    }
    return result;
  }
  
  protected StateUpdate instantiate(StateUpdate stUpd)
  {
    warningManager().warn("Pending generic type instantiation of state update within process signature.");
    return factory().deepCloneTerm(stUpd);
  }

  protected ProcessSignature instantiate(ProcessSignature signature)
  {
    // avoid individual checks for each case. just use the signature's structure
//    if (signature.isBasicProcessSignature())
//    {
//      getStateSignature()
//        getBasicProcessLocalZSignatures()
//        getActionSignatures()
//    }
//    else
//    {
//      getFormalParamsOrIndexes()
//      getCircusProcessChannelSets() 
//    }
    
    //{ getName(), getGenFormals(), getSignatureList(), getProcessChannelSets(), getStateUpdate(), getUsage() };
        
    // clone generic formals
    ZNameList genFormals = factory().deepCloneTerm(signature.getGenFormals());    
    List<? extends SignatureList> sigs = instantiate(signature.getSignatureList());
    ChannelSetList instChanSets = instantiate(signature.getProcessChannelSets());
    StateUpdate instStUpd = instantiate(signature.getStateUpdate());
    
    ProcessSignature result = factory().getCircusFactory().createProcessSignature(
      signature.getProcessName(), genFormals, sigs, instChanSets, instStUpd, 
      signature.getCallUsage());    
    return result;
  }
  
  /**
   * Get the list of strokes to add for local variable declaration. 
   * That is, add a variable with each stroke in the list (x', x?, ...), 
   * rather than one variable with all strokes (x'?...).
   */
  protected ZStrokeList getCircusStrokeListForLocalVars()
  {
    ZStrokeList zsl = factory().createZStrokeList();
    zsl.add(factory().createNextStroke());
    zsl.add(factory().createInStroke());
    zsl.add(factory().createOutStroke());
    return zsl;
  }
  
  protected List<NameTypePair> addStateVars(List<NameTypePair> pairs)
  {
    List<NameTypePair> result = factory().list();
    int i = 1;
    for(NameTypePair pair : pairs)
    {
      result.addAll(addStateVars(pair, i));
      i++;
    }
    return result;
  }
  
  protected void checkCircusNameStrokes(NameTypePair pair, int pos)
  {
    checkCircusNameStrokes(pair.getName(), pair.getType(), pos);
  }
  
  protected void checkCircusNameStrokes(Name name, Type type, int pos)
  {
    if (name instanceof ZName)
    {
      checkCircusNameStrokes(ZUtils.assertZName(name), type, pos);
    }
  }
  
  /**
   * Checks the given variable name does not have strokes, since Circus names
   * should not have then. The parser avoids mostly all cases, yet one could 
   * mistakely create names with strokes. It is joker-aware.
   * @param name the actual name to check for strokes. 
   * @param type the name type for a better warning message
   * @param pos the position where the name appears (or -1 for unknown)
   */
  protected void checkCircusNameStrokes(ZName name, Type type, int pos)
  {
    if ((name.getStrokeList() instanceof ZStrokeList) &&
             !name.getZStrokeList().isEmpty())
    {
      List<Object> errorParams = factory().list();
      errorParams.add(isWithinProcessParaScope() ? getCurrentProcessName() : "none");
      errorParams.add(isWithinActionParaScope() ? getCurrentActionName() : "none");
      errorParams.add(name);
      errorParams.add(type);      
      errorParams.add(pos == -1 ? "unknown" : pos);
      warningManager().warn(name, WarningMessage.CIRCUS_DECLNAMES_SHOULD_NOT_HAVE_STROKES, errorParams);
    }
  }
  
  protected void checkCircusNameStrokes(List<NameTypePair> pairs)
  {
    // warn about the presence of strokes on declaring names
    // as this is for warning purposes only, go gentle when
    // jokers might be around. (?)
    int i = 1;
    for(NameTypePair pair : pairs)
    {
      checkCircusNameStrokes(pair, i);
      i++;          
    }
  }

  /**
   * Adds local variables to the process scope. That means
   * adding four new variables for each name type pair given.
   * For example, for (x, T), we add x, x', x?, x! with type T.
   * That is needed in order to put right variables into context
   * for various operations. See B.26 ExtractVars
   */
  protected List<NameTypePair> addStateVars(NameTypePair pair, int pos)
  {
    // add the original variable name "x" to the scope
    List<NameTypePair> result = factory().list(pair);

    ZName varName = pair.getZName();
    Type varType = pair.getType();
    
    // if original name had strokes raise warning
    checkCircusNameStrokes(varName, varType, pos);
    
    ZStrokeList zsl = getCircusStrokeListForLocalVars();
    for (Stroke stroke : zsl)
    {      
      // create new variable with unique ID, hence ZDeclName, and the given stroke.      
      ZName strokedName = factory().createZDeclName(
        varName.getWord(), factory().createZStrokeList(factory().list(stroke)));
      NameTypePair strokedPair = factory().createNameTypePair(strokedName,
        varType);
      result.add(strokedPair);
    }
    assert (result.size() == zsl.size()+1) :
      "Local variable declarations must add " + (zsl.size() + 1) + " variables into scope.";

    // add them all into scope
    typeEnv().add(result);

    return result;
  }
  
  /**
   * Local variables are all those under current scope that are not UnknownType or CircusType
   * @param name
   * @return
   */
  protected boolean isLocalVar(ZName name)
  {   
    // if the type is known, it is a local variable only if not a Circus Type
    Type type = getLocalType(name);
    return isLocalVar(type);
  }
  
  /**
   * Local variables are all those under current scope that are not UnknownType or CircusType
   * @param name
   * @return
   */
  protected boolean isLocalVar(Type type)
  {
    boolean result = (type != null &&      
      !(type instanceof UnknownType) &&
      !(type instanceof CircusType));
   return result;
  }
  
  /**
   * Adds to the current scope all variables from a state paragraph's signature.
   * That is, it calls {@link #addStateVars(List;lt&NameTypePair;gt&)} for all 
   * pairs within the given signature.
   * @param signature state paragraph signature
   * @return resulting signature with all state variables (and their variants) added to the process global scope.
   */
  protected Signature addStateVars(SchemaType schemaType)
  {    
    List<NameTypePair> result = factory().list();
    int i = 1;
    // for each pair add 4 variables into global scope
    for(NameTypePair pair : schemaType.getSignature().getNameTypePair())      
    {
      result.addAll(addStateVars(pair, i));
      i++;
    }    
    Signature sig = factory().createSignature(result);
    return sig;
  }

  /**
   * Retrieves a type projection from a product type from the given offset (inclusive)
   * with the corresponding number of types. It obbeys the general Java invariant for
   * indexOf. To retrieve the remainder of the product type from an offset, just call
   * getProdTypeProjection(type, offset, size - offset).
   */
  protected Type2 getProdTypeProjection(List<Type2> prodTypes, int offset, int count)
  {
    List<Type2> innerTypes = factory().list(prodTypes.subList(offset, offset + count));
    assert !innerTypes.isEmpty() : "type projection resulted in an empty type.";
    Type2 result = innerTypes.size() > 1 ? factory().createProdType(innerTypes) : innerTypes.get(0);

    return result;
  }

  protected NameTypePair lastUsedChannelDecl()
  {
    throw new UnsupportedOperationException("cannot call last used channel directly, but only through a Communication checker");
  }
  
  /**
   * Typechecks the assignment pairs of either a rename process or action.
   * It raises an exception if called with invalid term (e.g., one different from
   * a rename process or action). The assignment pairs are given, and the result
   * communication list is filled (TODO).
   * @param term
   * @param apairs
   * @param commList
   */
  protected void typeCheckRenameListAssignmentPairs(Term term, CircusCommunicationList commList)
  {
    assert term != null && commList != null : "invalid term (null) or communication list (null)";
    
        
    boolean isProcess;
    AssignmentPairs apairs;
    if (term instanceof RenameProcess)
    {
      isProcess = true;
      // make sure we can use getCurrentProcessName()
      checkProcessParaScope(term, null);
      apairs = ((RenameProcess)term).getAssignmentPairs();
    }
    else if (term instanceof RenameAction)
    {
      isProcess = false;
      // make sure we can use getCurrentProcessName() and getCurrentActionName()
      checkActionParaScope(term, null);      
      apairs = ((RenameAction)term).getAssignmentPairs();
    }
    else
    {
      throw new IllegalArgumentException("Invalid term for typeCheckRenameListAssignmentPairs. Neither process, nor action rename.");
    }
    
    
    
    // the parser enforces              #ln1 = #ln2    
    ZNameList lhs = apairs.getZLHS();
    ZExprList rhs = apairs.getZRHS();

    // check for duplicate names and their local scope    
    List<NameTypePair> channelNames = factory().list();

    // check no duplicate names in the renaming list
    checkForDuplicateNames(lhs, term);

    // check the names in the rename list are channel names
    int i = 1;
    for (Name name : lhs)
    {
      // get the type - globally
      Type type = getGlobalType(name);
      if (type instanceof ChannelType)
      {
        channelNames.add(factory().createNameTypePair(name, type));
      }
      else
      {
        if (isProcess)
        {
          Object[] params = { getCurrentProcessName(), name, i, type };
          error(term, ErrorMessage.IS_NOT_CHANNEL_NAME_IN_RENAME_PROCESS, params);
        }
        else
        {
          Object[] params = { getCurrentProcessName(), getCurrentActionName(), name, i, type };
          error(term, ErrorMessage.IS_NOT_CHANNEL_NAME_IN_RENAME_ACTION, params);
        }        
      }
      i++;
    }

    // their sizes is enforced by the parser, by double check here
    // for the case of manually created assignments
    if (lhs.size() != rhs.size())
    {
      String value = (isProcess ? "process renaming" : ("action renaming for " + getCurrentActionName()));
      Object[] params = {
        getCurrentProcessName(), 
        value, lhs.size(), rhs.size()
      };
      error(term, ErrorMessage.UNBALANCED_ASSIGNMENT_PAIRS, params);
    }
    else
    {
      i = 1;
      Iterator<Expr> itExpr = rhs.iterator();
      for (NameTypePair ntp : channelNames)
      {
        // get the values
        assert itExpr.hasNext();

        Expr expr = itExpr.next();
        Type2 expected = GlobalDefs.unwrapType(ntp.getType());
        Type2 found = expr.accept(exprChecker());

        if (!unify(found, expected).equals(UResult.SUCC))
        {
          if (isProcess)
          {
            Object[] params = {
              getCurrentProcessName(),
              ntp.getName(), i, expected, found
            };
            error(term, ErrorMessage.RENAME_PROCESS_LIST_DONT_UNIFY, params);
          }
          else
          {
            Object[] params = {
              getCurrentProcessName(), getCurrentActionName(),
              ntp.getName(), i, expected, found
            };
            error(term, ErrorMessage.RENAME_ACTION_LIST_DONT_UNIFY, params);
          }
        }
        i++;
      }
      itExpr = null;
    }
    
    checkCircusNameStrokes(channelNames);
    
    // TODO: used channels/communications must change deep down into all actions! Oh my god!
    if (isProcess)
    {
      warningManager().warn("Process signature for rename process still requires update on all used communications." +
        "\n\tProcess...: {0}", getCurrentProcessName());
    }
    else
    {
      warningManager().warn("Process signature for rename process still requires update on all used communications." +
        "\n\tProcess...: {0}\n\tAction....: {1}", getCurrentProcessName(), getCurrentActionName());
    }
  }
  
  /***********************************************************************
   * Syntax validation methods 
   **********************************************************************/

//  
//  protected boolean isProcess(Name name)
//  {
//    boolean result = false;
//    for (ProcessInfo process : processes())
//    {
//      Name decl = process.getProcessName();
//      if (GlobalDefs.compareName(decl, name, true))
//      {
//        result = true;
//        break;
//      }
//    }
//    return result;
//  }
//  
//  protected boolean isGenericProcess(Name name)
//  {
//    boolean result = false;
//    for (ProcessInfo process : processes())
//    {
//      Name decl = process.getProcessName();
//      if (GlobalDefs.compareName(decl, name, true))
//      {
//        if(process.isGeneric())
//        {
//          result = true;
//          break;
//        }
//      }
//    }
//    return result;
//  }
//  
//  protected boolean isChannelSet(/*Ref*/Name name)
//  {
//    boolean result = false;
//    for (Name chanset : ZUtils.assertZNameList(chansets()))
//    {
//      if (ZUtils.assertZName(chanset).getWord().equals(
//        ZUtils.assertZName(name).getWord()))
//      {
//        result = true;
//        break;
//      }
//    }
//    return result;
//  }
//  // TODO: Check: why check getWord() at times but the whole object (with equals)
//  //              at other times? Why not checking always with equals (to ignore strokes?)
//  //              If that is okay, then it would avoid the ZDeclName casts and problems!
//  //              If that is not okay, then either use ZDeclName/ZRefName as formal parameters
//  //              or use DeclName and, while casting the object in the method code, either
//  //              throw a particular exception (i.e. TypeCheckerException) or just allow the
//  //              ClassCastException itself.
//  //
//  //              PS: Everywhere in CZT, apart from rewriting rule related tools, ZDeclName
//  //                  is always used, so that is okay to cast in the typechecker to ZDeclName.
//  //                  Other child classes for DeclName that is not ZDeclName, could be a
//  //                  JokerDeclName used during term rewriting.
//  protected boolean addChannel(Name name, Type type)
//  {
//    boolean result = true;
//    for (ChannelInfo channel : channels())
//    {
//      if (channel.getChannelType().getDeclName().equals(name))
//      {
//        channel.getChannelType().setType(type);
//        result = false;
//      }
//    }
//    
//    if(result)
//    {
//      NameTypePair nameType = factory().createNameTypePair(name, type);
//      ChannelInfo insert = new ChannelInfo(nameType);
//      channels().add(insert);
//    }
//    
//    return result;
//  }
//  
//  protected boolean addGenChannel(Name name, Type type, List<Name> params)
//  {
//    boolean result = true;
//    for (ChannelInfo channel : channels())
//    {
//      if (channel.getChannelType().getDeclName().equals(name))
//      {
//        channel.getChannelType().setType(type);
//        result = false;
//      }
//    }
//    
//    if(result)
//    {
//      NameTypePair nameType = factory().createNameTypePair(name, type);
//      ChannelInfo insert = new ChannelInfo(nameType, true, params);
//      channels().add(insert);
//    }
//    
//    return result;
//  }
//  
//  protected boolean addChannelSet(Name name)
//  {    
//    boolean result = !ZUtils.assertZNameList(chansets()).contains(name);
//    if(result)
//    {
//      ZUtils.assertZNameList(chansets()).add(name);
//    }    
//    return result;
//  }
//  /**
//   * Adds the given name type pair into the current type information scope,
//   * provided the name hasn't been declared in the current scope yet. It also
//   * adds stroked variations of the given name according to the strokes 
//   * returned by #getCircusStrokeListForStateVar (i.e. ', ?, !).
//   * 
//   * In case there is a naming conflict, the result is null. 
//   * Otherwise, it contains the list of names that generated the conflict.
//   * (i.e. "result = null || !result.isEmpty()" is part of the postcondition)
//   */
//  public List<ZName> addStateVar(NameTypePair pair)
//  { 
//    assert false : "TODO";
//    ZName varName = pair.getZName();    
//    Type varType = pair.getType();      
//    
//    List<ZName> existingNames = getFactory().list();
//    NameTypePair existing = getPair(varName);
//    
//    
//    // TODO: take this into account error(term, ErrorMessage.REDECLARED_STATEVAR_NAME, params);
//    
//    //if not already declared, add this declaration to the environment
//    //together with its getCircusStrokeListForStateVar()+1 (=4) variations    
//    if (existing == null)
//    { 
//      // add the original variable name to the scope, say "v"
//      List<NameTypePair> stateVars = getFactory().list();
//      stateVars.add(pair);      
//      
//      ZStrokeList zsl = getCircusStrokeListForStateVar();
//      for(Stroke stroke : zsl)
//      { 
//        // create a stroked version " v'/v?/v! " with same ID as "v" (just like Z tc does) in getDeltaXiType(...)
//        ZName strokedName = getFactory().createZName(varName, true);      
//        strokedName.getZStrokeList().add(stroke);
//        NameTypePair strokedPair = getFactory().createNameTypePair(strokedName, varType);
//        
//        // check whether the pair could have been created previously (very unlikely, but...)
//        existing = getPair(strokedName);
//        // if not, add it to the stateVars
//        if (existing == null)
//        {
//          stateVars.add(strokedPair);
//        }
//        // otherwise add the name for a complete error message
//        else
//        {
//          existingNames.add(varName);
//          existing.setType(varType);      
//        }
//      } 
//      
//      // if no new variable already existed, then add then all to the type environment
//      if (existing == null)
//      {
//        assert (stateVars.size() == zsl.size() + 1) :
//          "State variable declarations must add " + (zsl.size() + 1) + 
//          " variables in total.";
//        
//        // add all four variations to the type environment.
//        add(stateVars);
//      }
//    }
//    //otherwise, overwrite the existing declaration, and note that
//    //this declaration is a duplicate (i.e. result = false)
//    else
//    {      WRONG: this should be done later, elsewhere.
//      existingNames.add(varName);
//      existing.setType(varType);      
//    } 
//    
//    // if there were some duplicate pair, raise the error
//    if (/*existing != null ||*/ !existingNames.isEmpty())
//    {
//      assert existing != null;
//      //Object [] params = {existingNames.toString()};
//      //error(term, ErrorMessage.REDECLARED_STATEVAR_NAME, params);
//      return existingNames;
//    }
//    else
//    {
//      return null;
//    }
//  }  
//  protected ProcessInfo getProcessInfo(Name name)
//  {
//    ProcessInfo result = null;
//    List<ProcessInfo> processes = processes();
//    for(ProcessInfo proc : processes)
//    {
//      if(proc.getProcessName().equals(name))
//      {
//        result = proc;
//      }
//    }
//    return result;
//  }
//  
//  protected String getKindOfProcess(Name name)
//  {
//    String result = "";
//    for (ProcessInfo process : processes())
//    {
//      Name decl = process.getProcessName();
//      if (GlobalDefs.compareName(decl, name, true))
//      {
//        result = process.getKindOfProcess().name();
//        break;
//      }
//    }
//    return result;
//  }
//  
//  /**
//   * Check whether the given local name is fresh within the current
//   * local type environment scope.
//   *
//   * @param name the name to verify
//   * @return true if local name is fresh, false otherwise
//   */
//  protected boolean isLocalNameFresh(Name name)
//  {
//    boolean result = true;    
//    Type typeLocal = localCircTypeEnv().getType(ZUtils.assertZName(name));    
//    if(!(typeLocal instanceof UnknownType))
//    {
//      result = false;
//    }
//    return result;
//  }
//  
//  protected List<NameTypePair> getUsedChannels(Name procName)
//  {
//    List<NameTypePair> result = new ArrayList<NameTypePair>();
//    for(ProcessInfo proc : processes())
//    {
//      if(proc.getProcessName().equals(procName))
//      {
//        result.addAll(proc.getUsedChans());
//        break;
//      }
//    }
//    return result;
//  }
//  
//  protected List<Name> getGenParamsProcess(Name procName)
//  {
//    List<Name> result = new ArrayList<Name>();
//    for(ProcessInfo proc : processes())
//    {
//      if(proc.getProcessName().equals(procName))
//      {
//        result = proc.getGenParams();
//        break;
//      }
//    }
//    return result;
//  }
//  
//  public void addMuProcess(Name name)
//  {
//    muProcesses().add(name);
//  }
//  
//  public void addMuAction(Name name)
//  {
//    muActions().add(name);
//  }
//  
//  public void addAction4PostCheck(Name name)
//  {
//    actions4PostCheck().add(name);
//  }
//  
//  public void removeMuProcess(Name name)
//  {
//    for(Name nameMuProc : muProcesses())
//    {
//      if(nameMuProc.equals(name))
//      {
//        muProcesses().remove(name);
//        break;
//      }
//    }
//  }
//  
//  public void removeMuAction(Name name)
//  {
//    for(Name nameMuAct : muActions())
//    {
//      if(nameMuAct.equals(name))
//      {
//        muActions().remove(name);
//        break;
//      }
//    }
//  }
//  
//  public void removeAction4PostCheck(Name name)
//  {
//    for(Name act : actions4PostCheck())
//    {
//      if(act.equals(name))
//      {
//        actions4PostCheck().remove(name);
//        break;
//      }
//    }
//  }
//  
//  public boolean isMuProcess(Name name)
//  {
//    boolean result = false;
//    for(Name nameMuProc : muProcesses())
//    {
//      if(nameMuProc.equals(name))
//      {
//        result = true;
//        break;
//      }
//    }
//    return result;
//  }
//  
//  public boolean isMuAction(Name name)
//  {
//    boolean result = false;
//    for(Name nameMuAct : muActions())
//    {
//      if(nameMuAct.equals(name))
//      {
//        result = true;
//        break;
//      }
//    }
//    return result;
//  }
//  

  protected void error(Term term, ErrorMessage errorMsg, Object... params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, errorMsg, params);
    error(term, errorAnn);
  }

  protected void error(Term term, ErrorMessage errorMsg, List<Object> params)
  {
    error(term, errorMsg, params.toArray());
  }

  @Override
  protected void error(Term term,
    net.sourceforge.czt.typecheck.z.ErrorMessage error,
    Object[] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error.toString(), params);
    error(term, errorAnn);
  }

  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object... params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
      sectName(), GlobalDefs.nearestLocAnn(term), markup());
    return errorAnn;
  }

  @Override
  protected ErrorAnn errorAnn(Term term, String error, Object[] params)
  {
    // this method is very important to make sure the right "ErrorAnn" is created!
    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
      sectName(), GlobalDefs.nearestLocAnn(term),
      markup());
    return errorAnn;
  }

  //the local TypeEnv
  //protected net.sourceforge.czt.typecheck.circus.util.TypeEnv circusTypeEnv()
  //{
  //  return (net.sourceforge.czt.typecheck.circus.util.TypeEnv) typeEnv();
  //}

  //add generic types from a list of Names to the TypeEnv
//  protected void addGlobalGenParamTypes(List<Name> declNames)
//  {
//    assert false : "TODO";
//    //add each DeclName and its type
//    List<String> names = new ArrayList<String>();
//    for (Name declName : declNames)
//    {
//      ZName zdn = ZUtils.assertZName(declName);
//      GenParamType genParamType = factory().createGenParamType(zdn);
//      PowerType powerType = factory().createPowerType(genParamType);
//
//      //check if a generic parameter type is redeclared
//      if (names.contains(zdn.getWord()))
//      {
//        Object[] params = {declName};
//        error(declName, net.sourceforge.czt.typecheck.z.ErrorMessage.REDECLARED_GEN, params);
//      }
//      else
//      {
//        names.add(zdn.getWord());
//      }
//
//      //add the name and type to the TypeEnv
//      sectTypeEnv().add(zdn, powerType);
//    }
//  }

  /** 
   * Adds a new process signature annotation for given Term or update an existing one.
   */
  protected void addProcessSignatureAnn(CircusProcess term,
    ProcessSignature psig)
  {
    assert psig != null && isWithinProcessParaScope() : "cannot add process signature annotation outside process scope";

    // TODO: check if this won't be an error for mutually recursive processes.
    //assert psig.getName() == null ||
    //  ZUtils.namesEqual(getCurrentProcessName(), psig.getName()) : "resolved process signature is set to a different process than the one currently in scope";

    // sets the process name within the signature
    //psig.setProcessName(getCurrentProcessName());

    // retrieve signature ann within the term.
    ProcessSignatureAnn psigAnn = (ProcessSignatureAnn) term.getAnn(ProcessSignatureAnn.class);

    // update the inner term or create a new 
    if (psigAnn == null)
    {
      psigAnn = factory().getCircusFactory().createProcessSignatureAnn(psig);
      term.getAnns().add(psigAnn);
    }
    else
    {
      psigAnn.setProcessSignature(psig);
    }
  }

  /** 
   * Adds a new action signature annotation for given Term or update an existing one.
   */
  protected void addActionSignatureAnn(CircusAction term, ActionSignature asig)
  {
    assert asig != null && isWithinActionParaScope() : "cannot add action signature annotation outside action scope";

      // for action calls, their signatures must have the name of their call
      //(term instanceof CallAction) => ZUtils.namesEqual(asig.getName(), GlobalDefs.callAction(term).getName())
      //&& 
      // for Mu actions, their signatures must have the name of their recursive variable
      //(term instanceof MuAction) => ZUtils.namesEqual(asig.getName(), GlobalDefs.muAction(term).getName());
    
    //assert ((term instanceof CallAction) ? ZUtils.namesEqual(asig.getName(), GlobalDefs.callAction(term).getName()) :
    //  ((term instanceof MuAction) ? ZUtils.namesEqual(asig.getName(), GlobalDefs.muAction(term).getName()) :
    //    (asig.getName() == null || ZUtils.namesEqual(getCurrentActionName(), asig.getName()))))
    //  : "resolved action signature is set to a different action than the one currently in scope ";

    // sets the action name within the signature    
    if (term instanceof CallAction)
    {
      // for calls, their signature is related to the call
      asig.setActionName(((CallAction)term).getName());
    }
    else 
    {
      // for all others, get the current action being declared
      asig.setActionName(getCurrentActionName());
    }

    // retrieve signature ann within the term.
    ActionSignatureAnn asigAnn = (ActionSignatureAnn) term.getAnn(ActionSignatureAnn.class);

    // update the inner term or create a new 
    if (asigAnn == null)
    {
      asigAnn = factory().getCircusFactory().createActionSignatureAnn(asig);
      term.getAnns().add(asigAnn);
    }
    else
    {
      asigAnn.setActionSignature(asig);
    }
  }

  /**
   * <p>
   * These isometric resolution matrixes are used to figure out where is the
   * problem for parameterised calls, if any. To do this, we check the signature
   * of the calling action type against the CallAction expressions.
   * </p>
   * <p>
   * The first CALL_TYPE matrix distinguishes normal calls from either non-parameterised 
   * calls or wrong number of parameters, where an inconclusive solutions leads
   * to the next CALL_PARAMS matrix. 
   * </p>
   * <p>
   * Finally, the CALL_PARAMS matrix further distinguishes normal parameterised calls 
   * from call with either wrong number of parameters, or non-unifiable calling types
   * with respect to the action signature.
   * </p>
   * <p>
   * This trick avoids too many if/else statements, clarifies the code, and
   * allegedly is faster in general since ifs are all resolved at once (this case 
   * at each matrix). The same solution applies for action and process calls.
   * </p>
   */
  protected enum CallResolution
  {

    NormalCall,
    NormalParamCall,
    NotParameterisedCall,
    WrongNumberParameters,
    IncompatibleParamType,
    Inconclusive
  }

  
  
         ;

  static final  CallResolution    
           [][] CALL_TYPE = 
      {                             /* sig.isEmpty                           !sig.isEmpty  */
        /* call.isEmpty          */  { CallResolution.NormalCall           , CallResolution.WrongNumberParameters },  
        /* !call.isEmpty         */  { CallResolution.NotParameterisedCall , CallResolution.Inconclusive          } 
      };//                                                        |        
        //                                       |----------------|
        //                                       v 
  //protected static final CallResolution[][] CALL_PARAMS = 
  //    {                             /* sig.size  = call.size                 sig.size != call.size */
  //      /* paramUnify(sig, call) */  { CallResolution.NormalParamCall      , CallResolution.WrongNumberParameters },  
  //      /* !paramUnify(sig, call)*/  { CallResolution.IncompatibleParamType, CallResolution.WrongNumberParameters } 
  //   };
  // PS: to maximise number of error detection, we do not use the CALL_PARAMS. It is here mostly for documenetaion.
  
  protected List<? extends Type2> checkActualParameters(ZExprList actuals)
  {    
    List<Type2> result = factory().list();
    for(Expr expr : actuals)
    {
      // during postchecking, we want to avoid retypechecking - to avoid concurrent modification in paraErrors()      
      Type2 type = getType2FromAnns(expr);
      if (type instanceof UnknownType)
      {
        type = expr.accept(exprChecker());
      }
      result.add(type);            
    }
    assert result.size() == actuals.size() : "number of resolved actuals differ from given actuals";
    return result;
  }

  /**
   * Checks the given call, either an action or process call, is well formed.
   * That includes checking number of parameters, their types, the structure 
   * of the underlying call, and so on. The resulting value is a list of error
   * annotatiosn that MUST be raise by whoever call this method.   
   * See checkCallActionConsistency for more detailed documentation.
   * 
   * @param call the call term
   * @param resolvedFormals the resolved formals
   * @param actuals the resolved actuals
   * @return list of error annotations to be raised by the callee.
   */
  protected List<ErrorAnn> checkCallParameters(Term call,
    List<NameTypePair> resolvedFormals, ZExprList actuals, boolean checkProcessScope)
  {
    List<ErrorAnn> result = factory().list();

    assert (!checkProcessScope || isWithinProcessParaScope()) : "calls must be at least within process scope";

    // check the kind of call
    //boolean isActionCall = isWithinActionParaScope(); // at post checking this isn't true :-(
    //assert isActionCall ? (call instanceof CallAction) : (call instanceof CallProcess);
    
    // TODO: decouple the code a bit more so that we can have postchecking code separated from normal code on calls.
    boolean isActionCall = (call instanceof CallAction);
    assert (call instanceof CallAction) || 
           (call instanceof CallProcess) : "unknown kind of call to check parameters " + call;

    // create a default error list
    List<Object> params = factory().list();
    params.add(getCurrentProcessName());

    if (isActionCall)
    {
      params.add(getCurrentActionName());
    }
    params.add(call);

    // retrieve the type of call being checked.
    CallResolution callRes = CALL_TYPE[actuals.isEmpty() ? 0 : 1][resolvedFormals.isEmpty() ? 0 : 1];
    switch (callRes)
    {
      case NormalCall:
        // all is well. - empty result
        break;
      case NotParameterisedCall:
      case WrongNumberParameters:
        params.add(resolvedFormals.size());
        params.add(actuals.size());
        ErrorAnn err0 = errorAnn(call,
            (isActionCall ? ErrorMessage.PARAM_ACTION_CALL_DIFF_NUMBER_EXPRS : 
                            ErrorMessage.PARAM_PROC_CALL_DIFF_NUMBER_EXPRS),
            params.toArray());
          result.add(err0);
        break;                
      case Inconclusive:
        // deliberately check for the actuals, even if sizes are incompatible
        // this maximases the number of errors discovered. returns null if failed.
        List<? extends Type2> resolvedActuals = checkActualParameters(actuals);

        if (resolvedFormals.size() == resolvedActuals.size())
        {
          // case NormalParamCall:
          // assume everything will be ok from here -- result is empty
          assert result.isEmpty() : "Non empty list of errors in call parameter check, when it should be empty.";
          
          // case IncompatibleParamType: 
          for (int i = 0; i < resolvedFormals.size(); i++)
          {
            NameTypePair pair = resolvedFormals.get(i);
            Type2 expectedFormal = GlobalDefs.unwrapType(pair.getType());
            Type2 foundActual = GlobalDefs.unwrapType(resolvedActuals.get(i));
            if (foundActual instanceof UnknownType)
            {
              params.add(i + 1);
              params.add(expectedFormal);
              ErrorAnn err1 = errorAnn(call,
                (isActionCall ? ErrorMessage.PARAM_ACTION_CALL_UNDECLARED_VAR : 
                                ErrorMessage.PARAM_PROC_CALL_UNDECLARED_VAR),
                params.toArray());
              result.add(err1);
            }
            else
            {
              UResult unified = unify(foundActual, expectedFormal);
              if (!unified.equals(UResult.SUCC))
              {
                params.add(pair.getName());
                params.add(i + 1);
                params.add(expectedFormal);
                params.add(foundActual);                
                ErrorAnn err2 = errorAnn(call,
                  (isActionCall ? ErrorMessage.PARAM_ACTION_CALL_DNOT_UNIFY : 
                                  ErrorMessage.PARAM_PROC_CALL_DNOT_UNIFY),
                  params.toArray());
                result.add(err2);
              }
            // else, this param is ok, result is true.
            }
          }
        // if error is found, result will be false.
        }
        // else, leave the next case to catch wrong parameters number.                        
        else
        {
          //case WrongNumberParameters:
          params.add(resolvedFormals.size());
          params.add(actuals.size());
          ErrorAnn err3 = errorAnn(call,
            (isActionCall ? ErrorMessage.PARAM_ACTION_CALL_DIFF_NUMBER_EXPRS : 
                            ErrorMessage.PARAM_PROC_CALL_DIFF_NUMBER_EXPRS),
            params.toArray());
          result.add(err3);
        }
        break;      
      default:
        // takes care of NormalParamCall and IncompatibleParamType  
        // --- and NormalParamCall and IncompatibleParamType, which should only be dealt with in the inner case
        throw new AssertionError("should never reach this point in call type resolution --- " + callRes);
    }
    return result;
  }

  /**
   * Checks the consistency of the call by checking that the call type from the
   * current type environment correspond to the call name itself. It also checks
   * the call actual parameters for type consistency with respect to the declared
   * formals from the action type. This method is also used at post checking to
   * guarantee mutually recursive actions are well typed. 
   * <p>
   * As during  postchecking it is not allowed to add error annotations, we 
   * return an error annotation, if any.  This solution is not the neatest, 
   * but the simplest. Tha is, instead of having two different methods, one for
   * post checking and one for normal checking, doing the same work, we generalise 
   * it and make the error ann result. Whoever call this method MUST raise the
   * error, if any.
   * </p>
   * 
   * to the 
   * @param callType
   * @param term
   */
  protected List<ErrorAnn> checkCallActionConsistency(Type2 callType, CallAction term)
  {
    // typecheck the parameters in any case - this makes sure that postchecking 
    // can reuse typechecked expressions, hence doesn't add postcheck errors.
    checkActualParameters(term.getZExprList());
    
    List<ErrorAnn> result = factory().list();
    if (callType instanceof ActionType)
    {
      ActionType aType = (ActionType) callType;
      ActionSignature aSig = aType.getActionSignature();

      // if the signature refers to the call name, we are on
      if (ZUtils.namesEqual(term.getName(), aSig.getActionName()))
      {
        ZExprList actuals = term.getZExprList();
        List<NameTypePair> resolvedFormals = aSig.getFormalParams().getNameTypePair();
        List<ErrorAnn> callParamErrors = checkCallParameters(term, 
          resolvedFormals, actuals, true /* checkProcessScope */);
        result.addAll(callParamErrors);
      }
      // otherwise this is a awkward (type checker protocol) error. (?)
      else
      {
        Object[] params = {getCurrentProcessName(), getCurrentActionName(), term};
        result.add(errorAnn(term, ErrorMessage.IS_NOT_ACTION_NAME, params));
      }
    }
    else
    {
      // still give a chance to recover.
      Object[] params = {getCurrentProcessName(), getCurrentActionName(), term};
      SchemaType schemaType = referenceToSchema(callType);
      if (schemaType != null) 
      {
        // checks the schema expression
        List<ErrorAnn> stateScopeErrors = checkStateVarsScopeInSchExprAction(term, schemaType);
        result.addAll(stateScopeErrors);
        
        // TODO: have a parameterised typechecking to make this an error or not?
        warningManager().warn(term, WarningMessage.SCHEXPR_CALL_ACTION_WITHOUT_BRACKET, params);        
      }
      else
      {        
        result.add(errorAnn(term, ErrorMessage.IS_NOT_ACTION_NAME, params));
      }
    }
    return result;
  }
  
  protected List<ErrorAnn> checkCallProcessConsistency(Type2 callType, CallProcess term, boolean checkProcessScope)
  {
    // typecheck the parameters in any case - this makes sure that postchecking 
    // can reuse typechecked expressions, hence doesn't add postcheck errors.
    checkActualParameters(term.getZActuals());
    
    List<ErrorAnn> result = factory().list();
    if (callType instanceof ProcessType)
    {
      ProcessType pType = (ProcessType) callType;
      ProcessSignature pSig = pType.getProcessSignature();

      //System.out.println("checkCallProcessConsistency - " + term.getCallExpr() + "; " + pSig);
      
      // if the signature refers to the call name, we are on
      if (ZUtils.namesEqual(term.getCallExpr().getName(), pSig.getProcessName()))
      {        
        if (!pSig.getCallUsage().equals(term.getCallUsage()))
        {
          Object[] params = {
            getCurrentProcessName(),            
            term.getCallExpr().getName(),
            pSig.getCallUsage(),
            term.getCallUsage()              
          };
          result.add(errorAnn(term, ErrorMessage.PROCESS_USAGE_INCONSISTENCY, params));
        }  
        ZExprList actuals = term.getZActuals();
        
        // basic process cannot have formal parameters or indexes in their signatures
        // basic processes declared with parameters have a signature with parameters
        // and one inner process signature for the basic process within
        List<NameTypePair> resolvedFormals = pSig.isBasicProcessSignature() ? 
          factory().<NameTypePair>list() : pSig.getFormalParamsOrIndexes().getNameTypePair();
        List<ErrorAnn> callParamErrors = checkCallParameters(term, resolvedFormals, actuals, checkProcessScope);
        result.addAll(callParamErrors);
      }
      // otherwise this is a awkward (type checker protocol) error. (?)
      else
      {
        Object[] params = {getCurrentProcessName(), term};
        result.add(errorAnn(term, ErrorMessage.IS_NOT_PROCESS_NAME, params));
      }
    }
    else
    {
      Object[] params = {getCurrentProcessName(), term};
      result.add(errorAnn(term, ErrorMessage.IS_NOT_PROCESS_NAME, params));      
    }
    return result;
  }

  /**
   * Raise all the errors from the given list that were generated during 
   * the typechecking of the given term. This is to be called by all visiting
   * methods that used any of the general methods returning list of errors. 
   * This is important to avoid concurrent modification exceptions within 
   * the Z PostChecking protocol. 
   * 
   * @param term
   * @param list
   */
  protected void raiseErrors(Term term, List<ErrorAnn> list)
  {
    // raise all the errors from the list by adding them to the paraErrors()
    for(ErrorAnn e : list)
    {
      error(term, e);
    }
  }
  
  protected List<Pair<Name, List<ErrorAnn>>> pendingCallErrors()
  {
    return getCircusTypeChecker().pendingCallErrors_;
  }
  
  @Override
  protected void postCheck()
  {
    super.postCheck();
    pendingCallErrors().clear();
  }
  
  @Override
  protected void clearErrors(int fromIndex)
  {
    super.clearErrors(fromIndex);
    pendingCallErrors().clear();
  }
  
  protected List<ErrorAnn> getPendingCallErrors(Name call)
  {
    for(Pair<Name, List<ErrorAnn>> pair : pendingCallErrors())
    {
      if (ZUtils.namesEqual(call, pair.getFirst()))
        return pair.getSecond();
    }
    return null;
  }
  
  protected void appendCallErrors(Name call, List<ErrorAnn> callErrors)
  { 
    if (!callErrors.isEmpty())
    {
      List<ErrorAnn> errors = getPendingCallErrors(call);
      if (errors == null)
      {
        errors = factory().list(callErrors);
        pendingCallErrors().add(Pair.getPair(call, errors));
      }
      else 
      {
        // this updated the pendingCallErrors()
        errors.addAll(callErrors);
      }
    }
  }

//  protected ActionSignature joinActionSignature(Action2 term,
//    ActionSignature actionSigL, ActionSignature actionSigR)
//  { 
//    // action names cannot be resolved (i.e., name = null) when joining signatures
//    // unless it is a MuAction (i.e., name != null).
//    Name leftName = actionSigL.getActionName();
//    Name rightName = actionSigR.getActionName();    
//    boolean leftIsMu = actionSigL.getSignatureOfMuAction();
//    boolean rightIsMu = actionSigL.getSignatureOfMuAction();
//    
//    // if left is a MuAction, it is badly resolved if the name is unknown.
//    // otherwise, if left is a normal action, it is badly resolved if known
//    boolean leftBadlyResolved = (leftIsMu ? leftName == null : leftName != null);
//    boolean rightBadlyResolved = (rightIsMu ? rightName == null : rightName != null);
//    
//    // if both are badly resolved - it is okay if the names equal
//    boolean bothOk = leftBadlyResolved && rightBadlyResolved && ZUtils.namesEqual(leftName, rightName);
//        
////    if (!bothOk && (leftBadlyResolved || rightBadlyResolved))
////    {      
////      StringBuilder reason = new StringBuilder("resolved action name on ");
////      if (leftBadlyResolved && rightBadlyResolved)
////      {
////        reason.append("both sides: L=");
////        reason.append(leftIsMu ? "nameless MuAction" : leftName);
////        reason.append("; R=");
////        reason.append(rightIsMu ? "nameless MuAction" : rightName);        
////      } 
////      else if (leftBadlyResolved)
////      {
////         reason.append("left side: " + (leftIsMu ? "nameless MuAction" : leftName));
////      }
////      else// if (rightBadlyResolved)
////      {
////        reason.append("right side: " + (rightIsMu ? "nameless MuAction" : rightName));
////      }      
////      Object[] params = {
////        getCurrentProcessName(),
////        getCurrentActionName(),        
////        reason
////      };
////      error(term, ErrorMessage.INVALID_ACTION_SIGNATURE_JOIN, params);
////    }
//    
//
//    // formal parameters must be empty for joint signatures, unless their sides are calls
//    // (i.e., on-the-fly actions are also just calls). So, if the parameters are not empty
//    // then L/R elements MUST be calls (i.e., !(!isEmpty() => isCall) )
//    boolean leftFormalsBadlyResolved = 
//      !actionSigL.getFormalParams().getNameTypePair().isEmpty() && 
//      !(term.getLeftAction() instanceof CallAction);
//    boolean rightFormalsBadlyResolved = 
//      !actionSigR.getFormalParams().getNameTypePair().isEmpty() && 
//      !(term.getRightAction() instanceof CallAction);
//    if (leftFormalsBadlyResolved || rightFormalsBadlyResolved)
//    {
//      Object[] params = {
//        getCurrentProcessName(),
//        getCurrentActionName(),
//        ("non-empty formal parameters on " + 
//          (leftFormalsBadlyResolved && rightFormalsBadlyResolved ? "both sides" :
//            (leftFormalsBadlyResolved ? "left side" : "right side")) +
//            " for non-call action")
//      };
//      error(term, ErrorMessage.INVALID_ACTION_SIGNATURE_JOIN, params);
//    }
//
//    // create an empty signature as the result, but with proper place holders
//    // so that getFormalParams
//    // keep the action name unknown (null)
//    ActionSignature result = factory().createEmptyActionSignature();
//
//    // local variables are ignored, since the scope is local ;-)
//    // formal parameters are ignored, sine they cannot appear during signature join
//
//    // get channel declarations from each side
//    GlobalDefs.addAllNoDuplicates(actionSigL.getUsedChannels().getNameTypePair(), result.getUsedChannels().getNameTypePair());
//    GlobalDefs.addAllNoDuplicates(actionSigR.getUsedChannels().getNameTypePair(), result.getUsedChannels().getNameTypePair());    
//    
//    // get used name sets from each side without duplication
//    GlobalDefs.addAllNoDuplicates(actionSigL.getUsedNameSets(), result.getUsedNameSets());
//    GlobalDefs.addAllNoDuplicates(actionSigR.getUsedNameSets(), result.getUsedNameSets());    
//    
//    // get used channel sets from each side
//    GlobalDefs.addAllNoDuplicates(actionSigL.getUsedChannelSets(), result.getUsedChannelSets());
//    GlobalDefs.addAllNoDuplicates(actionSigR.getUsedChannelSets(), result.getUsedChannelSets());    
//    
//    // get communications from each side
//    GlobalDefs.addAllNoDuplicates(actionSigL.getUsedCommunications(), result.getUsedCommunications());
//    GlobalDefs.addAllNoDuplicates(actionSigR.getUsedCommunications(), result.getUsedCommunications());    
//    
//    return result;
//  }

  protected StateUpdate joinStateUpdate(CircusProcess term, StateUpdate leftState, StateUpdate rightState)
  {
    warningManager().warn("State update merge is still to be implemented. For now just return the left side.");
    StateUpdate result = leftState;
    return result;
  }
  
//  protected ProcessSignature joinProcessSignature(Process2 term,
//    ProcessSignature processSigL, ProcessSignature processSigR)
//  { 
//    // process names cannot be resolved (i.e., name = null) when joining signatures    
//    Name leftName = processSigL.getProcessName();
//    Name rightName = processSigR.getProcessName();
//    boolean leftBadlyResolved = leftName != null;
//    boolean rightBadlyResolved = rightName != null;
//    
//    // if both are badly resolved - it is okay if the names equal
//    boolean bothOk = leftBadlyResolved && rightBadlyResolved && ZUtils.namesEqual(leftName, rightName);
//        
////    if (!bothOk && (leftBadlyResolved || rightBadlyResolved))
////    {      
////      StringBuilder reason = new StringBuilder("resolved process name on ");
////      if (leftBadlyResolved && rightBadlyResolved)
////      {
////        reason.append("both sides: L=");
////        reason.append(leftName);
////        reason.append("; R=");
////        reason.append(rightName);        
////      } 
////      else if (leftBadlyResolved)
////      {
////         reason.append("left side: " + leftName);
////      }
////      else// if (rightBadlyResolved)
////      {
////        reason.append("right side: " + rightName);
////      }      
////      Object[] params = {
////        getCurrentProcessName(),        
////        reason
////      };
////      error(term, ErrorMessage.INVALID_PROCESS_SIGNATURE_JOIN, params);
////    }
//    
//    // if either is true exclusively (Java xor), then there is a problem
//    boolean leftIndexed = processSigL.getUsage().equals(CallUsage.Indexed);
//    boolean rightIndexed = processSigR.getUsage().equals(CallUsage.Indexed);
//    if (leftIndexed ^ rightIndexed)
//    {
//      Object[] params = { 
//        getCurrentProcessName(), 
//        ("left side has " + (leftIndexed ? "indexes" : "formal parameters") +
//          "but right side has " + (rightIndexed ? "indexes" : "formal parameters"))
//      };
//      error(term, ErrorMessage.INVALID_PROCESS_SIGNATURE_JOIN, params);
//    }
//    
//    // formal parameters must be empty for joint signatures, unless their sides are calls
//    // (i.e., on-the-fly processes are also just calls). So, if the parameters are not empty
//    // then L/R elements MUST be calls (i.e., !(!isEmpty() => isCall) )
//    boolean leftFormalsBadlyResolved = 
//      !processSigL.isBasicProcessSignature() &&
//      !processSigL.getFormalParamsOrIndexes().getNameTypePair().isEmpty() && 
//      !(term.getLeftProcess() instanceof CallProcess);
//    boolean rightFormalsBadlyResolved = 
//      !processSigR.isBasicProcessSignature() &&
//      !processSigR.getFormalParamsOrIndexes().getNameTypePair().isEmpty() &&
//      !(term.getRightProcess() instanceof CallProcess);
//    if (leftFormalsBadlyResolved || rightFormalsBadlyResolved)
//    {
//      // TODO:DESIGN: TO DECIDE: this avoids the presence of NESTED parameters and indexes for now      
//      StringBuilder reason = new StringBuilder("non-empty ");      
//      if (leftFormalsBadlyResolved && rightFormalsBadlyResolved)
//      {
//        reason.append(leftIndexed ? "indexes" : "formal parameters");
//        reason.append(" for non-call process on left side, and non-empty ");
//        reason.append(rightIndexed ? "indexes" : "formal parameters");
//        reason.append(" for non-call process on right side");
//      }
//      else if (leftFormalsBadlyResolved)
//      {
//        reason.append(leftIndexed ? "formal parameters" : "indexes");
//        reason.append(" for non-call process on left side");
//      }
//      else // if (rightFormalsBadlyResolved)
//      {
//        reason.append(leftIndexed ? "formal parameters" : "indexes");
//        reason.append(" for non-call process on right side");
//      }                    
//      Object[] params = { getCurrentProcessName(), reason};
//      error(term, ErrorMessage.INVALID_PROCESS_SIGNATURE_JOIN, params);
//    }
//    
//    boolean leftGenericsPresent = !processSigL.getGenFormals().isEmpty();
//    boolean rightGenericsPresent = !processSigL.getGenFormals().isEmpty();
//    if (leftGenericsPresent || rightGenericsPresent)
//    {     
//      Object[] params = { 
//        getCurrentProcessName(), 
//        ("non-empty generic formals on " + 
//          (leftFormalsBadlyResolved && rightFormalsBadlyResolved ? "both sides" :
//            (leftFormalsBadlyResolved ? "left side" : "right side")))
//      };
//      error(term, ErrorMessage.INVALID_PROCESS_SIGNATURE_JOIN, params);
//    }
//
//    // create an empty signature as the result, but with proper place holders    
//    ProcessSignature result = factory().createEmptyProcessSignature();
//    
//    // formal parameters and generics are ignored, sine they cannot appear during signature join
//            
//    // join their state updates
//    StateUpdate stateUpdate = joinStateUpdate(term, 
//      processSigL.getStateUpdate(), processSigR.getStateUpdate());
//    result.setStateUpdate(stateUpdate);
//        
//    // add all the process signatures for non-basic process    
//    // i.e., basic processes will have getProcessSignatures() empty.
//    assert !processSigL.isBasicProcessSignature() || processSigL.getProcessSignatures().isEmpty() 
//      : "confused process signature - both basic and non-basic process: at left side of joinProcessSignature";
//    assert !processSigR.isBasicProcessSignature() || processSigR.getProcessSignatures().isEmpty()
//    : "confused process signature - both basic and non-basic process: at right side of joinProcessSignature";
//    result.getProcessSignatures().addAll(processSigL.getProcessSignatures());
//    result.getProcessSignatures().addAll(processSigR.getProcessSignatures());
//    
//    // if any side is the signature of a basic process "on-the-fly", then add it directly
//    // get channel declarations from each side depending on whether they are basic procs or not    
//    if (processSigL.isBasicProcessSignature())
//    {
//      result.getProcessSignatures().add(processSigL);
//    }
//    else
//    {
//      GlobalDefs.addAllNoDuplicates(processSigL.getCircusProcessChannelSets(), result.getCircusProcessChannelSets());    
//    }
//    if (processSigR.isBasicProcessSignature())
//    {
//      result.getProcessSignatures().add(processSigR);
//    } 
//    else
//    {
//      GlobalDefs.addAllNoDuplicates(processSigR.getCircusProcessChannelSets(), result.getCircusProcessChannelSets());    
//    }
//    /*
//    if (result.isBasicProcessSignature())
//    {
//      result.getBasicProcessLocalZSignatures().addAll(processSigL.getBasicProcessLocalZSignatures());
//      result.getBasicProcessLocalZSignatures().addAll(processSigR.getBasicProcessLocalZSignatures());    
//    }*/
//    
//    // the other inner entities are related to either BasicProcess or general processes,
//    // in which case we DO NOT MERGE signatures. That is because there are semantical
//    // considerations to be made for merging two such processes 
//    // (see e.g., Circus Refinement Calculus, Law C.146, p. 213
//    //  http://www.cs.york.ac.uk/ftpdir/reports/YCST-2006-02.pdf)
//    
//    // for a complete access to all elements deep down the tree of possibilities,
//    // one need to use one of the auxiliary (recursive) methods within ProcessSignature,
//    // which return maps from Action names to the corresponding lists
//    
//    return result;
//  }
  
  /**
   * This implements Manuela's "NoRep" function (see B.52, p.136).
   * It is a stronger version of "z.Checker.checkForDuplicates", 
   * which would accept declarations like "x: \nat; x: \num" since 
   * both types would unify.
   */
  protected void checkForDuplicateNames(ZNameList declNames, Term term)
  {    
    Map<String, ZName> map = factory().hashMap();
    int i = 1;
    Iterator<Name> iter = declNames.iterator();
    while (iter.hasNext())
    {
      ZName first = ZUtils.assertZName(iter.next());
      String firstName = ZUtils.toStringZName(first);
      ZName second = map.get(firstName);
      if (second != null)
      {
        //merge the ids of the 2 names, and remove the duplicate
        factory().merge(second, first);
        iter.remove();
        
        Object[] params = { getConcreteSyntaxSymbol(term), second, i};
        error(term, ErrorMessage.DUPLICATE_NAME_DECLARATION_LIST, params);
      }
      map.put(firstName.intern(), first);
      i++;
    }
    iter = null;
  }
  
  protected void checkForDuplicateNames(List<NameTypePair> pairs, Term term)
  {
    ZNameList znl = factory().createZNameList();
    for(NameTypePair ntp : pairs)
    {
      znl.add(ntp.getName());
    }
    checkForDuplicateNames(znl, term);
  }
  
  protected CircusCommunicationList visit(CircusAction term)     
  {
    if ((term instanceof MuAction) && 
        ((MuAction)term).isParameterised() && 
        actionCheckerVisitCount_ != 0)
    {
      Object[] params = { getCurrentProcessName(), getCurrentActionName(), ((MuAction)term).getName() };      
      error(term, ErrorMessage.INVALID_PARAMETERISED_MUACTION_PLACEMENT, params);
    }    
    actionCheckerVisitCount_++;
    return term.accept(actionChecker());
  }  
  
//  protected void checkForNestedFormals(Term term, CircusAction action, ActionSignature aSig)
//  {
//    // if nesting is present, raise an error - it isn't allowed
//    // unless this is call action, in which case parameters may be present    
//    boolean formalsAreBadlyFormed = 
//       (!(action instanceof CallAction) &&
//       !aSig.getFormalParams().getNameTypePair().isEmpty())
//       //||    
//       //((action instanceof MuAction) && 
//       // (((MuAction)action).getCircusAction() instanceof ParamAction) &&
//       // ((ParamAction)((MuAction)action).getCircusAction()).
//       // !aSig.getFormalParams().getNameTypePair().isEmpty()
//       //)
//       ;
//    if (formalsAreBadlyFormed)
//    {
//      Object[] params = {
//        getCurrentProcessName(),
//        getCurrentActionName()        
//      };
//      error(term, ErrorMessage.NESTED_FORMAL_PARAMS_IN_ACTION, params);
//    }
//  }
  
  /**
   * Given an action name and its body, checks it for consistency. First checks
   * if it is within a process paragraph scope. This sets the typechecker state for  the
   * current action name to be the one given, provided such name is Unknown or a MuAction
   * (i.e., the name is not being redeclared or it is of a MuAction being currently declared).
   * Next, nesting of actions is checked, where only MuActions are allowed to declared
   * nested action contexts. Finally, the action is checked and its signature returned.
   * 
   * @param aName the action name to declare
   * @param action the action definition associated with the name
   * @param term the term where the definition is being added (e.g., ActionPara, MuAction)
   * @return the typechecked action signature for the given action
   */
  protected ActionSignature checkActionDecl(Name aName, CircusAction action, Term term)
  {
    // check process paragraph scope.
    checkProcessParaScope(term, aName);
    
    ActionSignature aSig = factory().createEmptyActionSignature();
    
    // TODO: CHECK: if this redeclared business is needed
    // TODO: CHECK: not sure if this is a good idea because it may annotate
    //              aName with an UnderclaredAnn ? Not if directly from typeEnv()
    //              rather than Checker.getType(aName);    
    Type type = getLocalType(aName);
    if ((type instanceof UnknownType) || (term instanceof MuAction))
    {
      // set current action name being checked.
      // this opens a action para scope, which is cleared at the end.
      // Actions can only be checked within an opened action para scope.
      Name old = setCurrentActionName(aName);
      CircusAction oldAction = setCurrentAction(action);
      ActionSignature oldSignature = actionChecker().setCurrentActionSignature(aSig);
      // nesting is allowed only for MuAction.
      if (old != null && !(term instanceof MuAction))
      {
        Object[] params = { getCurrentProcessName(), aName, old };
        error(term, ErrorMessage.NESTED_ACTIONPARA_SCOPE, params);
      }

      // enter scope for local variables within an action paragraph    
      // since these are local to the process, they must be within 
      // the type environment.
      typeEnv().enterScope();

      // check the declared action updating its name on the returned action signature
      CircusCommunicationList commList = visit(action);
      
      // clone the inner term to avoid aliasing
      //aSig = factory().deepCloneTerm(actionSignature);
      aSig.setActionName(aName);      
      aSig.getUsedCommunications().addAll(0, commList);      
      
      // closes local vars and formal parameters scope
      typeEnv().exitScope();
      
      // restors the process para scope.
      old = setCurrentActionName(old);
      oldAction = setCurrentAction(oldAction);
      oldSignature = actionChecker().setCurrentActionSignature(oldSignature);
      assert old == aName && oldAction == action && oldSignature == aSig : "Invalid action para scoping for " + aName;      
    }
    else
    {      
      aSig.setActionName(aName);
      Object [] params = {aName, getConcreteSyntaxSymbol(term), getCurrentProcessName() };
      error(term, ErrorMessage.REDECLARED_DEF, params);      
    }        
    return aSig;
  }  
  
  /**
   * Checks the scope of the the schema type associated with the given action.
   * That is, checks the declared varaibles are within process scope (e.g., 
   * state or local variables). We are deliberately allowing SchExpr in call 
   * actions to be typechecked as schemas, even if they are not surounded by
   * the adequate brackets. Thus, we accept the given term as CircusAction.
   * 
   * @param term
   * @param schType
   * @return either the given schType, or in the case of variable signature, a new schema type with new ids.
   */
  protected List<ErrorAnn> checkStateVarsScopeInSchExprAction(CircusAction term, SchemaType schType)
  {    
    List<ErrorAnn> result = factory().list();
    Signature signature = schType.getSignature();

    // resolve any variable type
    if (!(signature instanceof VariableSignature))
    {
      Signature sig = createNewIds(signature);      
      schType.setSignature(sig);
      signature = sig;
    }

    // make sure all names are in (process) scope
    for (NameTypePair pair : signature.getNameTypePair())
    {
      // get type, but locally
      Type type = getLocalType(pair.getName());
      Type2 expected = GlobalDefs.unwrapType(type);

      // if type is unknown, raise an error
      if (expected instanceof UnknownType)
      {
        Object[] params = {getCurrentProcessName(), getCurrentActionName(), term, pair.getName()};
        result.add(errorAnn(term, ErrorMessage.SCHEXPR_ACTION_VAR_OUT_OF_SCOPE, params));
      }
      // otherwise unify with the type found
      else
      {
        Type2 found = GlobalDefs.unwrapType(pair.getType());
        UResult unified = unify(found, expected);
        // if doesn't unify, raise an error
        if (unified.equals(UResult.FAIL))
        {
          Object[] params = {getCurrentProcessName(), getCurrentActionName(),
            term, pair.getName(), expected, found
          };
          result.add(errorAnn(term, ErrorMessage.SCHEXPR_ACTION_FAIL_UNIFY, params));
        }        
      }
    }
    return result;
  }
  
  protected boolean easilyFinite(Expr expr)
  {
    // set displays are always finite, hence easily decidable
    boolean result = (expr instanceof SetExpr);
    if (!result)
    {
      // if this is a range (i.e. _ .. _), then it is also finite
      result = ZUtils.isFcnOpApplExpr(expr) && 
        ((RefExpr)ZUtils.getApplExprRef(expr)).getZName().getWord().equals(
        ZString.ARG_TOK+ ZString.DOT + ZString.DOT +ZString.ARG_TOK);
    }
    return result;
  }
  
  protected void addFinitenessProoofObligation(Term term, Expr expr)
  {
    Expr finiteExpr = factory().getZFactory().createRefExpr(
      factory().createZName(ZString.FINSET + ZString.ARG_TOK), 
      factory().getCircusFactory().createZExprList(factory().list(expr)), 
      true, false);
    Pred pred = factory().getCircusFactory().createMemPred(            
      factory().list(expr, finiteExpr), false);            
    CircusUtils.addProofObligationAnn(term, pred);
  }
  
  protected boolean isValidDeclClass(Decl decl)
  {
     // if it isn't the case that Decl is either VarDecl or
     // an allowed QualifiedDecl point, then raise the errors
     return ((GlobalDefs.instanceOf(decl, VarDecl.class) || 
       (isQualifiedParamAllowed() && 
       GlobalDefs.instanceOf(decl, QualifiedDecl.class))));
  }
  
  protected Expr getDeclExpr(Decl decl)
  {
    assert isValidDeclClass(decl) : "invalid decl class to extract expr - " + decl.getClass().getSimpleName();
    
    if (decl instanceof VarDecl)
      return ((VarDecl)decl).getExpr();
    else // if (decl instanceof QualifiedDecl)
      return ((QualifiedDecl)decl).getExpr();
  }
  
  protected NameList getDeclNames(Decl decl)
  {
    assert isValidDeclClass(decl) : "invalid decl class to extract decl names - " + decl.getClass().getSimpleName();
    
    if (decl instanceof VarDecl)
      return ((VarDecl)decl).getNameList();
    else // if (decl instanceof QualifiedDecl)
      return ((QualifiedDecl)decl).getNameList();
  }
  
  /**
   * Typechecks a declaration list for a circus production within the given term.
   * That is, either a declaration of a parameterised process/action/command or
   * iterated process/action. It checks for valid kinds of Decl classes allowed
   * by each case raising the appropriate error if needed. It cares about the case
   * whether finite declarations should be considered (i.e., adds a proof obligation
   * to the declaring expression and raise a warning if not possible decide automatically;
   * see #easilyFinite(Term) for that.). 
   * <p>
   * After that, the parameters are checked by the DeclChecker accordingly.
   * Potential generic types from a process declaration is added to the resulting 
   * list of name type pairs. Finally, the list is checked for duplicate names
   * or type mismatches. 
   * </p>
   * @param term term where decls come from
   * @param decls the decls to type check
   * @param considerFiniteness flag to consider finiteness of the type the declarations or not
   * @param allowQualifiedDecl flag that treats this declaration as a parameterised command or not.
   *          That is, if it is to consider QualifiedDecl from within the ZDeclList given or not.
   * @param errorMessage the error message to raise in case an invalid Decl is found 
   * @param errorParams the error parameters for errorMessage and WarningMessage.POTENTIALLY_INFINITE_INDEX in case considerFiniteness is true.
   * @return a list of name type pairs for the declared parameters considering potential generic types from the process scope.
   */
  protected List<NameTypePair> typeCheckCircusDeclList(Term term, 
    ZDeclList decls, boolean considerFiniteness, boolean allowQualifiedDecl, 
    ErrorMessage errorMessage, List<Object> errorParams)
  {
    // any circus declaration must at least be within some process scope.
    checkProcessParaScope(term, null);
    
    // flags to the DeclCheck we are declaring parameters - not allowing qualified Decl
    setCircusFormalParametersDecl(true, allowQualifiedDecl);
    
    assert errorParams != null && errorParams.size() >= 1
      : "Invalid error parameters in typeCheckCircusDeclList: it must have at least 1 element.";
    
    int i = 1;
    for(Decl d : decls)
    {
      if (isValidDeclClass(d))
      {
        // check if the iterators are finite, raising a warning if not.        
        Expr vdExpr = getDeclExpr(d);
        if (considerFiniteness && !easilyFinite(vdExpr))
        {     
          if (!isWithinActionParaScope())
          {
            errorParams.add("none");
          }
          errorParams.add(i);
          errorParams.add(getDeclNames(d));
          errorParams.add(vdExpr);
          warningManager().warn(term, WarningMessage.POTENTIALLY_INFINITE_INDEX, errorParams);                      
          addFinitenessProoofObligation(term, vdExpr);          
        }
      }
      else
      {
        errorParams.add(d);
        errorParams.add(i);
        errorParams.add(getConcreteSyntaxSymbol(d));        
        error(term, errorMessage, errorParams);        
      }
      i++;
    }
    
    // check the parameters
    List<NameTypePair> pairs = decls.accept(declChecker());    
   
    checkCircusNameStrokes(pairs);
    
    // return the flags back to normal after checking the parameters
    setCircusFormalParametersDecl(false, false);
    
    //Add the potential generics to the parameters type
    List<NameTypePair> gParams = addGenerics(pairs);
    
    // check for duplicate in the names
    checkForDuplicateNames(gParams, term);    
        
    // check for type mismatches in the parameters signature
    checkForDuplicates(gParams, factory().<Term>list(
      getCurrentProcessName(),  
      (isWithinActionParaScope() ? 
        getCurrentActionName() : factory().createZName("none"))), 
      ErrorMessage.TYPE_MISMATCH_IN_CIRCUS_DECL.toString());    
    
    return gParams;
  }    
  
  // carrier sets for channel and name sets have a type as \power~NS/CSType(CIRCUS_ID)
  private Type2 circusIdType_ = null;
  protected Type2 typeCheckCircusIdType()
  {
    if (circusIdType_ == null)
    {
      circusIdType_ = checkUnificationSpecialType(factory().createCircusIdName(), 
        factory().createCircusIdType());
      
      // adds type annotation to these circus expressions       
      CircusUtils.CIRCUS_ID_EXPR.accept(exprChecker());      
    }    
    return circusIdType_;
  }
  
  protected RefExpr circusIdExpr()
  {
    typeCheckCircusIdType();
    return CircusUtils.CIRCUS_ID_EXPR;
  }
  
  /**
   * Type checks channel sets for all productions raising errors if needed with the
   * given parameters, which MUST have exactly 2 parameters.
   * @param term
   * @param errorParams
   * @return
   */
  protected ChannelSetType typeCheckChannelSet(ChannelSet term, List<Object> errorParams)
  {        
    typeCheckCircusIdType();
    Type2 type = term.accept(exprChecker());    
    Type2 innerType = type;    
    if (type instanceof PowerType)
    {
      innerType = GlobalDefs.powerType(type).getType();
    }
     
    ChannelSetType result;
    if (innerType instanceof ChannelSetType)
    {
      result = (ChannelSetType)innerType;
    }
    else
    {
      result = factory().createChannelSetType();
      UResult unified = unify(innerType, result);    
      // if doesn't unify, then raise an error 
      if (unified.equals(UResult.FAIL))
      {      
        assert errorParams != null && errorParams.size() == 2 
          : "Invalid error parameters in typeCheckChannelSet: it must have 2 elements exactly.";
        errorParams.add(term);
        errorParams.add(type);               
        error(term, ErrorMessage.NON_CHANNELSET_IN_POWEREXPR, errorParams);      
      }
    }
    return result;
  }
  
  /**
   * Type checks name sets for all productions raising errors if needed with the
   * given parameters, which MUST have exactly 3 parameters.
   * @param term
   * @param errorParams
   * @return
   */
  protected NameSetType typeCheckNameSet(NameSet term, List<Object> errorParams)
  {    
    Type2 type = term.accept(exprChecker());    
    Type2 innerType = type;
    if (type instanceof PowerType)
    {
      innerType = GlobalDefs.powerType(type).getType();
    }
    
    NameSetType result;
    if (innerType instanceof NameSetType)
    {
      result = (NameSetType)innerType;
    }
    else
    {
      result = factory().createNameSetType();
      UResult unified = unify(innerType, result);    
      
      // if doesn't unify, then raise an error 
      if (unified.equals(UResult.FAIL))
      { 
        assert errorParams != null && errorParams.size() == 3 
          : "Invalid error parameters in typeCheckNameSet: it must have 3 elements exactly.";
        errorParams.add(term);
        errorParams.add(type);
        error(term, ErrorMessage.NON_NAMESET_IN_SETEXPR, errorParams);
      }
    }
    return result;
  }
  
  /**
   * Method called for predicat type checking. It raises a warning if not solved in the second run.
   * @param term
   * @param pred
   * @param solved
   */
  protected void typeCheckPred(Term term, Pred pred)
  {    
    UResult solved = pred.accept(predChecker());

    // if not solved in the first pass, do it again
    if (solved.equals(UResult.PARTIAL))
    {
      // try again - just like in Z
      solved = pred.accept(predChecker());
      
      // if not solved a second time, raise the warning 
      if (!solved.equals(UResult.SUCC))
      {
        warningManager().warn(term, WarningMessage.COULD_NOT_RESOLVE_PRED, 
          getConcreteSyntaxSymbol(term), term, pred);          
      }
    }
  }

  protected void addWarnings()
  { 
    errors().addAll(warningManager().warnErrors());
    warningManager().clearWarnErrors();
  }  
  
  protected Boolean getResult()
  {
    Boolean result = Boolean.TRUE;
    // if there are errors, make sure warnings are not considered
    if (errors().size() > 0) {      
      // if strict on warnings, then consider then as errors and return false
      result = !getCircusTypeChecker().getWarningManager().getWarningOutput().equals(WarningManager.WarningOutput.RAISE);

      // otherwise, give the result without considering warnings
      if (result)
      {
        Iterator<net.sourceforge.czt.typecheck.z.ErrorAnn> it = errors().iterator();
        while (it.hasNext() && result)
        {
          net.sourceforge.czt.typecheck.z.ErrorAnn error = it.next();
          // do not consider warnings
          result = !error.getErrorType().equals(ErrorType.ERROR);
        }
        it = null;
      }
    }
    return result;
  }
  
  protected Signature wrapTypeAndAddAnn(Name declName, Type type, Para term)
  {
    NameTypePair pair = factory().createNameTypePair(declName, type);
    Signature result = factory().createSignature(pair);    
    checkCircusNameStrokes(declName, type, 1);        
    addTypeAnn(term, type);  
    return result;
  }
}
