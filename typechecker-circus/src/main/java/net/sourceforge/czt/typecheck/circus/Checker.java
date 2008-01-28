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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionSignatureAnn;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessSignatureAnn;
import net.sourceforge.czt.circus.util.CircusConcreteSyntaxSymbol;
import net.sourceforge.czt.circus.util.CircusConcreteSyntaxSymbolVisitor;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.impl.VariableSignature;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.UndeterminedTypeException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GenParamType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * Derived superclass of all XXXChecker classes (i.e., one for each syntactic 
 * category). It provides general facilities for the derived checkers. This 
 * usually includes typeing environment lookup and update, factory methods,
 * syntax checks, and so on.
 *
 * @author Leo Freitas
 * @author Manuela Xavier
 */
public abstract class Checker<R>
  extends net.sourceforge.czt.typecheck.z.Checker<R>
{

  protected TypeChecker typeChecker_;

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    assert typeChecker != null;
    typeChecker_ = typeChecker;
  }

  /**
   * Gives access to the typechecking factory for all checkers. 
   * 
   * @return typechecking factory that takes variable types/signature into account.
   */
  protected net.sourceforge.czt.typecheck.circus.impl.Factory factory()
  {
    return typeChecker_.getFactory();
  }

  /**
   * Let var terms are important for proof obligation generators that require 
   * scoping information of local variables with their declared, rather than 
   * maximal, types.
   * @return determines if the typechecker should create let var terms or not.
   */
  protected boolean shouldCreateLetVar()
  {
    return typeChecker_.shouldCreateLetVars_;
  }

  /**
   * Let mu terms are important  for mutually recursive processes and actions.
   * @return determines if the typechecker should create let mu terms or not.
   */
  protected boolean shouldCreateLetMu()
  {
    return typeChecker_.shouldCreateLetMu_;
  }

  /***********************************************************************
   * Checker accessors per syntactic category
   **********************************************************************/
  protected Checker<ProcessSignature> processChecker()
  {
    return typeChecker_.processChecker_;
  }

  protected Checker<Signature> processParaChecker()
  {
    return typeChecker_.processParaChecker_;
  }

  protected BasicProcessChecker basicProcessChecker()
  {
    return typeChecker_.basicProcessChecker_;
  }
  
  protected Checker<ActionSignature> actionChecker()
  {
    return typeChecker_.actionChecker_;
  }

  protected Checker<List<NameTypePair>> commChecker()
  {
    return typeChecker_.commChecker_;
  }

  protected Checker<ActionSignature> commandChecker()
  {
    return typeChecker_.commandChecker_;
  }

  protected CircusConcreteSyntaxSymbolVisitor concreteSyntaxSymbolVisitor()
  {
    return typeChecker_.concreteSyntaxSymbolVisitor_;
  }

  protected WarningManager warningManager()
  {
    return typeChecker_.warningManager_;
  }
  
  // TODO
  protected Checker<Signature> signatureChecker()
  {
    return typeChecker_.signatureChecker_;
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
    return typeChecker_.currentProcessName_;
  }

  protected ZName getCurrentZProcessName()
  {
    return ZUtils.assertZName(getCurrentProcessName());
  }

  protected Name setCurrentProcessName(Name name)
  {
    Name old = typeChecker_.currentProcessName_;
    typeChecker_.currentProcessName_ = name;
    return old;
  }

  protected CircusProcess getCurrentProcess()
  {
    return typeChecker_.currentProcess_;
  }
  
  protected BasicProcess getCurrentBasicProcess()
  {
    CircusProcess result = getCurrentProcess();
    return (result instanceof BasicProcess ? (BasicProcess)result : null);
  }

  protected CircusProcess setCurrentProcess(CircusProcess process)
  {
    CircusProcess old = typeChecker_.currentProcess_;
    typeChecker_.currentProcess_ = process;
    return old;
  }

  /**
   * This flag must be set whenever we are performing typechecking 
   * over circus formal paramters. This is important to make sure 
   * only VarDecl or QualifiedDecl is allowed.
   */
  protected void setCircusFormalParametersDecl(boolean val)
  {
    typeChecker_.circusFormalParameters_ = val;
  }

  protected boolean isCheckingCircusFormalParamDecl()
  {
    return typeChecker_.circusFormalParameters_;
  }

  /**
   * Return whether the typechecker is within the scope of a process paragraph.
   * This is useful to check whether a process declaration can be analysed, or
   * to avoid nested scopes. The latter is already enforced by the parser.   
   */
  protected boolean isWithinProcessParaScope()
  {
    return typeChecker_.currentProcessName_ != null &&
      typeChecker_.currentProcess_ != null;
  }

  protected boolean checkProcessParaScope(Term term, Name name)
  {
    boolean result = isWithinProcessParaScope();
    if (!result)
    {
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add(getConcreteSyntaxSymbol(term));
      params.add(name != null ? name : "");
      error(term, ErrorMessage.INVALID_PROCESS_PARA_SCOPE, params);
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
    typeChecker_.onTheFlyProcesses_ = procs;
  }

  protected ZParaList onTheFlyProcesses()
  {
    return typeChecker_.onTheFlyProcesses_;
  }

  /***********************************************************************
   * Methods for the various action related information 
   **********************************************************************/
  protected Name getCurrentActionName()
  {
    return typeChecker_.currentActionName_;
  }

  protected ZName getCurrentZActionName()
  {
    return ZUtils.assertZName(getCurrentActionName());
  }

  protected Name setCurrentActionName(Name name)
  {
    Name old = typeChecker_.currentActionName_;
    typeChecker_.currentActionName_ = name;
    return old;
  }

  protected CircusAction getCurrentAction()
  {
    return typeChecker_.currentAction_;
  }

  protected CircusAction setCurrentAction(CircusAction action)
  {
    CircusAction old = typeChecker_.currentAction_;
    typeChecker_.currentAction_ = action;
    return old;
  }
  
  /**
   * 
   * @return
   */
  protected List<ActionPara> getCurrentOnTheFlyActions()
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
      typeChecker_.currentActionName_ != null &&
      typeChecker_.currentAction_ != null);
  }

  protected void checkActionParaScope(Term term, Name name)
  {
    if (!isWithinActionParaScope())
    {
      List<Object> params = factory().list();
      params.add(getCurrentProcessName());
      params.add(getConcreteSyntaxSymbol(term));
      params.add(name != null ? name : "");
      error(term, ErrorMessage.INVALID_ACTION_PARA_SCOPE, params);
    }
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
    Type2 found = GlobalDefs.unwrapType(sectTypeEnv().getType(name));
    
    assert !(found instanceof UnknownType) : "Special type " + name + 
      " must be known in the sect type environment before creating the checker.";
    
    UResult resolved = unify(expected, found);
    if (resolved.equals(UResult.SUCC))
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
    return typeChecker_.stateName_;
  }

  protected ZName getZStateName()
  {
    return ZUtils.assertZName(getStateName());
  }

  protected void setStateName(Name name)
  {
    typeChecker_.stateName_ = name;
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

    // wrap up the result base type as a channel type.
    for (NameTypePair pair : result)
    {
      Type2 type = GlobalDefs.unwrapType(pair.getType());
      ChannelType cType = factory().createChannelType(type);
      pair.setType(cType);
      
      // add channel type annotation to channel name
      addTypeAnn(pair.getName(), cType);
    }
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
  
  protected List<NameTypePair> addLocalVars(List<NameTypePair> pairs)
  {
    List<NameTypePair> result = factory().list();
    for(NameTypePair pair : pairs)
    {
      result.addAll(addLocalVars(pair));
    }
    return result;
  }

  /**
   * Adds local variables to the process scope. That means
   * adding four new variables for each name type pair given.
   * For example, for (x, T), we add x, x', x?, x! with type T.
   * That is needed in order to put right variables into context
   * for various operations. See B.26 ExtractVars
   */
  protected List<NameTypePair> addLocalVars(NameTypePair pair)
  {
    // add the original variable name "x" to the scope
    List<NameTypePair> result = factory().list(pair);

    ZName varName = pair.getZName();
    Type varType = pair.getType();

    ZStrokeList zsl = getCircusStrokeListForLocalVars();
    for (Stroke stroke : zsl)
    {
      // create new variable with unique ID, hence ZDeclName, combining 
      // its original strokes with the stroke to add here.
      ZStrokeList strokeList = factory().createZStrokeList();    
      strokeList.addAll(pair.getZName().getZStrokeList());
      strokeList.add(stroke);
      ZName strokedName = factory().createZDeclName(pair.getZName().getWord(),
        strokeList);
      NameTypePair strokedPair = factory().createNameTypePair(strokedName,
        varType);
      result.add(strokedPair);
    }
    assert (result.size() == zsl.size()) :
      "Local variable declarations must add " + (zsl.size() + 1) + " variables into scope.";

    // add them all into scope
    typeEnv().add(result);

    return result;
  }
  
  /**
   * Adds to the current scope all variables from a state paragraph's signature.
   * That is, it calls {@link #addLocalVars(List;lt&NameTypePair;gt&)} for all 
   * pairs within the given signature.
   * @param signature state paragraph signature
   * @return resulting signature with all state variables (and their variants) added to the process global scope.
   */
  protected Signature addStateVars(SchemaType schemaType)
  {    
    List<NameTypePair> result = factory().list();
    
    // for each pair add 4 variables into global scope
    for(NameTypePair pair : schemaType.getSignature().getNameTypePair())      
    {
      result.addAll(addLocalVars(pair));
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
  protected Type2 getProdTypeProjection(ProdType type, int offset, int count)
  {
    List<Type2> innerTypes = factory().list(type.getType().subList(offset, count));
    assert !innerTypes.isEmpty() : "type projection resulted in an empty type.";
    Type2 result = innerTypes.size() > 1 ? factory().createProdType(innerTypes) : innerTypes.get(0);

    return result;
  }

  protected NameTypePair lastUsedChannel()
  {
    throw new UnsupportedOperationException("cannot call last used channel directly, but only through a Communication checker");
  }

  /***********************************************************************
   * Syntax validation methods 
   **********************************************************************/
//  protected boolean isChannel(/*String name*/Name name)
//  {
//    boolean result = false;
//    for (ChannelInfo channel : channels())
//    {
//      Name decl = channel.getChannelType().getDeclName();
//      if (GlobalDefs.compareName(decl, name, true))
//      {
//        result = true;
//        break;
//      }
//    }
//    return result;
//  }
//  
//  // TODO: Check: why String at times and DeclName at other times?
//  protected boolean isGenericChannel(Name name)
//  {
//    boolean result = false;
//    for (ChannelInfo channel : channels())
//    {
//      Name decl = channel.getChannelType().getDeclName();
//      if (GlobalDefs.compareName(decl, name, true))
//      {
//        if(channel.isGeneric())
//        {
//          result = true;
//          break;
//        }
//      }
//    }
//    return result;
//  }
//  
//  protected List<Name> getGenParamsChannel(Name name)
//  {
//    List<Name> result = new ArrayList<Name>();
//    for (ChannelInfo channel : channels())
//    {
//      Name decl = channel.getChannelType().getDeclName();
//      if (GlobalDefs.compareName(decl, name, true))
//      {
//        result = channel.getParams();
//        break;
//      }
//    }
//    return result;
//  }
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
//  public boolean isLovalVar(Name name)
//  {
//    boolean result = true;
//    ZName zrn = ZUtils.assertZName(name);
//    Type type = typeEnv().getType(zrn);
//    if(!(type instanceof UnknownType))
//    {
//      ZName declName = factory().createZName(zrn.getWord());
//      if(localCircTypeEnv().isAction(declName) || localCircTypeEnv().isNameSet(declName))
//      {
//        result = false;
//      }
//    }
//    else
//    {
//      result = false;
//    }
//    return result;
//  }
//  
//  public boolean isLocalVars(List<Name> names)
//  {
//    boolean result = true;
//    for(Name name : names)
//    {
//      result = isLovalVar(name);
//      if(!result)
//      {
//        break;
//      }
//    }
//    return result;
//  }
  protected void error(Term term, ErrorMessage errorMsg, Object[] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, errorMsg, params);
    error(term, errorAnn);
  }

  protected void error(Term term, ErrorMessage errorMsg, List<Object> params)
  {
    error(term, errorMsg, params);
  }

  @Override
  protected void error(Term term,
    net.sourceforge.czt.typecheck.z.ErrorMessage error,
    Object[] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error.toString(), params);
    error(term, errorAnn);
  }

  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object[] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
      sectName(), nearestLocAnn(term),
      markup());
    return errorAnn;
  }

  @Override
  protected ErrorAnn errorAnn(Term term, String error, Object[] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
      sectName(), nearestLocAnn(term),
      markup());
    return errorAnn;
  }

  //the local TypeEnv
  protected net.sourceforge.czt.typecheck.circus.util.TypeEnv circusTypeEnv()
  {
    return (net.sourceforge.czt.typecheck.circus.util.TypeEnv) typeEnv();
  }

  //add generic types from a list of Names to the TypeEnv
  protected void addGlobalGenParamTypes(List<Name> declNames)
  {
    assert false : "TODO";
    //add each DeclName and its type
    List<String> names = new ArrayList<String>();
    for (Name declName : declNames)
    {
      ZName zdn = ZUtils.assertZName(declName);
      GenParamType genParamType = factory().createGenParamType(zdn);
      PowerType powerType = factory().createPowerType(genParamType);

      //check if a generic parameter type is redeclared
      if (names.contains(zdn.getWord()))
      {
        Object[] params = {declName};
        error(declName, ErrorMessage.REDECLARED_GEN, params);
      }
      else
      {
        names.add(zdn.getWord());
      }

      //add the name and type to the TypeEnv
      sectTypeEnv().add(zdn, powerType);
    }
  }

  /** 
   * Adds a new process signature annotation for given Term or update an existing one.
   */
  protected void addProcessSignatureAnn(CircusProcess term,
    ProcessSignature psig)
  {
    assert psig != null && isWithinProcessParaScope() : "cannot add process signature annotation outside process scope";

    // TODO: check if this won't be an error for mutually recursive processes.
    assert psig.getName() == null ||
      ZUtils.namesEqual(getCurrentProcessName(), psig.getName()) : "resolved process signature is set to a different process than the one currently in scope";

    // sets the process name within the signature
    psig.setProcessName(getCurrentProcessName());

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

  // TODO: do we need to check for variable type/signature within the process signature?
//      if (oldSignature instanceof VariableSignature &&
//          variableSignature(oldSignature).getValue() == oldSignature) {
//        variableSignature(oldSignature).setValue(signature);
//      }
//      else {
//        signatureAnn.setSignature(signature);
//      }    
  }

  /** 
   * Adds a new action signature annotation for given Term or update an existing one.
   */
  protected void addActionSignatureAnn(CircusAction term, ActionSignature asig)
  {
    assert asig != null && isWithinActionParaScope() : "cannot add action signature annotation outside action scope";

    // TODO: check if this won't be an error for mutually recursive processes.
    assert asig.getName() == null ||
      ZUtils.namesEqual(getCurrentActionName(), asig.getName()) : "resolved action signature is set to a different action than the one currently in scope";

    // sets the process name within the signature
    asig.setActionName(getCurrentActionName());

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

//  protected ProcessSignature joinProcessSignature(ProcessSignature procSigL, ProcessSignature procSigR)
//  {
//    
//    ProcessSignature result = factory().createProcessSignature();
//    BasicProcessSignature resultTemp = factory().createBasicProcessSignature();
//    
//    if(procSigL instanceof BasicProcessSignature)
//    {
//      BasicProcessSignature sigL = (BasicProcessSignature)procSigL;
//      if(sigL.getActionsSignature() != null)
//      {
//        resultTemp.getActionsSignature().addAll(sigL.getActionsSignature());
//      }
//      if(sigL.getDeclNameSets() != null)
//      {
//        resultTemp.getDeclNameSets().addAll(sigL.getDeclNameSets());
//      }
//      if(sigL.getLocalZDeclsSignature() != null)
//      {
//        resultTemp.getLocalZDeclsSignature().addAll(sigL.getLocalZDeclsSignature());
//      }
//      if(sigL.getStateSignature() != null)
//      {
//        if(resultTemp.getStateSignature() != null)
//        {
//          List<NameTypePair> pairs = sigL.getStateSignature().getNameTypePair();
//          List<NameTypePair> resultPairs = resultTemp.getStateSignature().getNameTypePair();
//          for(NameTypePair pair : pairs)
//          {
//            if(!resultPairs.contains(pair))
//            {
//              resultPairs.add(pair);
//            }
//          }
//          resultTemp.setStateSignature(factory().createSignature(resultPairs));
//        }
//        else
//        {
//          resultTemp.setStateSignature(sigL.getStateSignature());
//        }
//      }
//      result = resultTemp;
//    }
//    
//    if(procSigR instanceof BasicProcessSignature)
//    {
//      BasicProcessSignature sigR = (BasicProcessSignature)procSigR;
//      if(sigR.getActionsSignature() != null)
//      {
//        resultTemp.getActionsSignature().addAll(sigR.getActionsSignature());
//      }
//      if(sigR.getDeclNameSets() != null)
//      {
//        resultTemp.getDeclNameSets().addAll(sigR.getDeclNameSets());
//      }
//      if(sigR.getLocalZDeclsSignature() != null)
//      {
//        resultTemp.getLocalZDeclsSignature().addAll(sigR.getLocalZDeclsSignature());
//      }
//      if(sigR.getStateSignature() != null)
//      {
//        if(resultTemp.getStateSignature() != null)
//        {
//          List<NameTypePair> pairs = sigR.getStateSignature().getNameTypePair();
//          List<NameTypePair> resultPairs = resultTemp.getStateSignature().getNameTypePair();
//          for(NameTypePair pair : pairs)
//          {
//            if(!resultPairs.contains(pair))
//            {
//              resultPairs.add(pair);
//            }
//          }
//          resultTemp.setStateSignature(factory().createSignature(resultPairs));
//        }
//        else
//        {
//          resultTemp.setStateSignature(sigR.getStateSignature());
//        }
//      }
//      result = resultTemp;
//    }
//    
//    if(procSigL.getParamsOrIndexes() != null)
//    {
//      if(result.getParamsOrIndexes() != null)
//      {
//        List<NameTypePair> pairs = procSigL.getParamsOrIndexes().getNameTypePair();
//        List<NameTypePair> resultPairs = result.getParamsOrIndexes().getNameTypePair();
//        for(NameTypePair pair : pairs)
//        {
//          if(!resultPairs.contains(pair))
//          {
//            resultPairs.add(pair);
//          }
//        }
//        result.setParamsOrIndexes(factory().createSignature(resultPairs));
//      }
//      else
//      {
//        result.setParamsOrIndexes(procSigL.getParamsOrIndexes());
//      }
//    }
//    if(procSigR.getParamsOrIndexes() != null)
//    {
//      if(result.getParamsOrIndexes() != null)
//      {
//        List<NameTypePair> pairs = procSigR.getParamsOrIndexes().getNameTypePair();
//        List<NameTypePair> resultPairs = result.getParamsOrIndexes().getNameTypePair();
//        for(NameTypePair pair : pairs)
//        {
//          if(!resultPairs.contains(pair))
//          {
//            resultPairs.add(pair);
//          }
//        }
//        result.setParamsOrIndexes(factory().createSignature(resultPairs));
//      }
//      else
//      {
//        result.setParamsOrIndexes(procSigR.getParamsOrIndexes());
//      }
//    }
//    
//    return result;
//    
//  }
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

  protected static final  CallResolution    
  
       
        
    
         
      
    
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
      Type2 type = expr.accept(exprChecker());
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
    List<NameTypePair> resolvedFormals, ZExprList actuals)
  {
    List<ErrorAnn> result = factory().list();

    assert isWithinProcessParaScope() : "calls must be at least within process scope";

    // check the kind of call
    boolean isActionCall = isWithinActionParaScope();
    assert isActionCall ? (call instanceof CallAction) : (call instanceof CallProcess);

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
        result.add(errorAnn(call, 
          (isActionCall ? ErrorMessage.IS_NOT_PARAM_ACTION_IN_ACTION_CALL : ErrorMessage.IS_NOT_PARAM_PROCESS_IN_PROC_CALL),
          params.toArray()));
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
              ErrorAnn err = errorAnn(call,
                (isActionCall ? ErrorMessage.PARAM_ACTION_CALL_UNDECLARED_VAR : 
                                ErrorMessage.PARAM_PROC_CALL_UNDECLARED_VAR),
                params.toArray());
              result.add(err);
            }
            else
            {
              UResult unified = unify(foundActual, expectedFormal);
              if (!unified.equals(UResult.SUCC))
              {
                params.add(pair.getName());
                params.add(expectedFormal);
                params.add(foundActual);
                params.add(i + 1);
                ErrorAnn err = errorAnn(call,
                  (isActionCall ? ErrorMessage.PARAM_ACTION_CALL_NOT_UNIFY : 
                                  ErrorMessage.PARAM_PROC_CALL_NOT_UNIFY),
                  params.toArray());
                result.add(err);
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
          ErrorAnn err = errorAnn(call,
            (isActionCall ? ErrorMessage.ACTION_CALL_DIFF_NUMBER_EXPRS : 
                            ErrorMessage.PROC_CALL_DIFF_NUMBER_EXPRS),
            params.toArray());
          result.add(err);
        }
        break;
      case WrongNumberParameters:
        params.add(resolvedFormals.size());
        ErrorAnn err = errorAnn(call,
          (isActionCall ? ErrorMessage.PARAM_ACTION_CALL_WITHOUT_EXPRS : 
                          ErrorMessage.PARAM_PROC_CALL_WITHOUT_EXPRS),
          params.toArray());
        result.add(err);
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
        List<ErrorAnn> callParamErrors = checkCallParameters(term, resolvedFormals, actuals);
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
        warningManager().warn(WarningMessage.SCHEXPR_CALL_ACTION_WITHOUT_BRAKET, params);        
      }
      else
      {        
        result.add(errorAnn(term, ErrorMessage.IS_NOT_ACTION_NAME, params));
      }
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

  protected ActionSignature joinActionSignature(CircusAction term,
    ActionSignature actionSigL, ActionSignature actionSigR)
  {
    // CHANGED: we could have MuAction with different names associated with the signature(?) TODO: CHECK:
    //
    // at this point, names are ignored (i.e. must be null)
    //if (actionSigL.getActionName() != null ||
    //  actionSigR.getActionName() != null)
    //{
    //  Object[] params = {
    //    getCurrentProcessName(),
    //    getCurrentActionName(),
    //    "resolved action names"
    //  };
    //  error(term, ErrorMessage.INVALID_ACTION_SIGNATURE_JOIN, params);
    //}

    // formal parameters must be empty for joint signatures    
    // on-the-fly actions are just calls, so should not have formal parameters.
    if (!actionSigL.getFormalParams().getNameTypePair().isEmpty() ||
      !actionSigR.getFormalParams().getNameTypePair().isEmpty())
    {
      Object[] params = {
        getCurrentProcessName(),
        getCurrentActionName(),
        "non-empty formal parameters"
      };
      error(term, ErrorMessage.INVALID_ACTION_SIGNATURE_JOIN, params);
    }

    // create an empty signature as the result, but with proper place holders
    // so that getFormalParams
    // keep the action name unknown (null)
    ActionSignature result = factory().createEmptyActionSignature();

    // local variables are ignored, since the scope is local ;-)
    // formal parameters are ignored, sine they cannot appear during signature join

    // join the communications of each side
    result.getUsedCommunications().addAll(actionSigL.getUsedCommunications());
    result.getUsedCommunications().addAll(actionSigR.getUsedCommunications());

    return result;

  }

  /**
   * This implements Manuela's "NoRep" function (see B.52, p.136).
   * It is a stronger version of "z.Checker.checkForDuplicates", 
   * which would accept declarations like "x: \nat; x: \num" since 
   * both types would unify.
   */
  protected void checkForDuplicateNames(ZNameList declNames,
    ErrorMessage errorMsg)
  {    
    Map<String, ZName> map = factory().hashMap();
    for (Iterator<Name> iter = declNames.iterator(); iter.hasNext();)
    {
      ZName first = ZUtils.assertZName(iter.next());
      String firstName = ZUtils.toStringZName(first);
      ZName second = map.get(firstName);
      if (second != null)
      {
        //merge the ids of the 2 names, and remove the duplicate
        factory().merge(second, first);
        iter.remove();
      }
      map.put(firstName.intern(), first);
    }
  }

  protected ActionSignature checkActionDecl(ZName aName, CircusAction action, Term term)
  {
    // check process paragraph scope.
    checkProcessParaScope(term, aName);
    
    ActionSignature aSig;
    
    // TODO: CHECK: not sure if this is a good idea because it may annotate
    //              aName with an UnderclaredAnn ? Not if directly from typeEnv()
    //              rather than Checker.getType(aName);    
    Type type = typeEnv().getType(aName);
    if ((type instanceof UnknownType) || (term instanceof MuAction))
    {
      // set current action name being checked.
      // this opens a action para scope, which is cleared at the end.
      // Actions can only be checked within an opened action para scope.
      Name old = setCurrentActionName(aName);
      CircusAction oldAction = setCurrentAction(action);
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
      aSig = action.accept(actionChecker());
      assert ZUtils.namesEqual(aSig.getActionName(), aName) : 
        "action signature built outside proper action para scope: found: " + 
        aSig.getActionName() + "; expected: " + aName;

      // closes local vars and formal parameters scope
      typeEnv().exitScope();

      // restors the process para scope.
      old = setCurrentActionName(old);
      oldAction = setCurrentAction(oldAction);
      assert old == aName && 
             oldAction == action : "Invalid action para scoping for " + aName;      
    }
    else
    {
      aSig = factory().createEmptyActionSignature();
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
      Type2 expected = GlobalDefs.unwrapType(getType(pair.getName()));

      if (expected instanceof UnknownType)
      {
        Object[] params = {getCurrentProcessName(), getCurrentActionName(), term, pair.getName()};
        result.add(errorAnn(term, ErrorMessage.SCHEXPR_ACTION_VAR_OUT_OF_SCOPE, params));
      }
      else
      {
        Type2 found = GlobalDefs.unwrapType(pair.getType());
        UResult unified = unify(found, expected);
        if (unified.equals(UResult.FAIL))
        {
          Object[] params = {getCurrentProcessName(), getCurrentActionName(),
            term, expected, found
          };
          result.add(errorAnn(term, ErrorMessage.SCHEXPR_ACTION_FAIL_UNIFY, params));
        }
      }
    }
    return result;
  }
}
