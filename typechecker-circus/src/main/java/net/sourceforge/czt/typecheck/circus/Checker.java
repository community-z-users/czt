/*
  Copyright (C) 2005, 2006, 2007 Leo Freitas
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
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.BasicProcessSignature;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.ZSignatureList;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.typecheck.circus.impl.ChannelInfo;
import net.sourceforge.czt.typecheck.circus.impl.ProcessInfo;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.circus.util.TypeEnv;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.GenParamType;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
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
  
  protected net.sourceforge.czt.typecheck.circus.impl.Factory factory()
  {
    return typeChecker_.getFactory();
  }
  
  protected boolean shouldCreateLetVar()
  {
    return typeChecker_.shouldCreateLetVars_;
  }
   
  /***********************************************************************
   * Checker accessors per syntactic category
   **********************************************************************/
  
  /* NOTE:
   * Various checker subclasses, one per syntactic category.
   * They are presented here in the order they were implemented.
   */
    
  // specChecker() -> DONE
  // paraChecker() -> DONE
  
  protected Checker<ProcessSignature> processChecker()
  {
    return typeChecker_.processChecker_;
  }
  
  // TODO
  protected Checker<Signature> signatureChecker()
  {
    return typeChecker_.signatureChecker_;
  }
  
  protected Checker<ActionSignature> actionChecker()
  {
    return typeChecker_.actionChecker_;
  }
  
  protected Checker<ActionSignature> commandChecker()
  {
    return typeChecker_.commandChecker_;
  }
  
  protected Checker<List<NameTypePair>> commChecker()
  {
    return typeChecker_.commChecker_;
  }  
  
  protected Checker<Boolean> channelDeclChecker()
  {
    return typeChecker_.channelDeclChecker_;
  }
  
  protected Checker<NameList> channelsUsedChecker()
  {
    return typeChecker_.channelsUsedChecker_;
  }

  protected Checker<Signature> processParaChecker()
  {
    return typeChecker_.processParaChecker_;
  }

  /** 
   * General method that checks whether the given name is typed with
   * the expected type Type class. If the type info stack does not have
   * type information for the given name, the result is obviously false
   * regardless of the expected class.
   */
  protected boolean isTypedAsExpected(Name name, Class<? extends Type> expected)
  {
    assert name != null && expected != null;
    
    // NOTE: Originally, Manuela used name comparison (possibly) without 
    //       considering strokes (see GlobalDefs.compareNames). This does
    //       not seem to make much sense and it wasn't well motivated. 
    //       In any case, TypeEnv.getType uses getX, which uses "namesEqual"
    //       method that does the right name comparison.
    
    // retrieve type information for given name
    Type type = getType(name);        
    
    // checks whether it is non-null and of the expected type    
    return expected.isInstance(type);
  }
  
   /** A name is a nameset if it has NameSetType */
  public boolean isChannel(Name name)
  {    
    return isTypedAsExpected(name, NameSetType.class);
  }
  
  /** A name is a nameset if it has NameSetType */
  public boolean isNameSet(Name name)
  {    
    return isTypedAsExpected(name, NameSetType.class);
  }
  
  /** A name is an action if it has ProcessType */
  public boolean isProcess(Name name)
  {
    return isTypedAsExpected(name, ProcessType.class);    
  }
  
  /** A name is an action if it has ActionType */
  public boolean isAction(Name name)
  {
    return isTypedAsExpected(name, ActionType.class);    
  }  
  
  /**
   * A name is a parameterised action if it has ActionType
   * and the formal parameters signature within the action 
   * signature is not empty.
   */
  public boolean isParamAction(Name name) 
  {    
    Type type = getType(name);
    boolean result = isAction(name)
    if (result)
    {      
      ActionType atype = (ActionType)type;
      result = !atype.getActionSignature().getFormalParams().getNameTypePair().isEmpty();
    }    
    return result;
  }
  
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
    return typeChecker_.currentProcess_;
  }
  
  protected ZName getCurrentZProcessName()
  {
    return ZUtils.assertZName(getCurrentProcessName());
  }
  
  protected Name setCurrentProcessName(Name name)
  {
    Name old = typeChecker_.currentProcess_;
    typeChecker_.currentProcess_ = name;
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
    return typeChecker_.currentProcess_ != null;
  }    
  
   
  protected void checkProcessParaScope(String paraKind, Name name)
  {
    boolean result = isWithinProcessParaScope();
    if (!result)
    {
      Object[] params = { paraKind, name };
      error(term, ErrorMessage.INVALID_PROCESS_PARA_SCOPE, params);      
    }
    return result;
  }
  
  /***********************************************************************
   * Methods for the on-the-fly process related information 
   **********************************************************************/  
  
  protected void setOnTheFlyProcesses(ZParaList procs)
  {
    typeChecker_.onTheFlyProcesses_= procs;
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
    return typeChecker_.currentAction_;
  }
  
  protected ZName getCurrentZActionName()
  {
    return ZUtils.assertZName(getCurrentActionName());
  }
  
  protected void setCurrentActionName(Name name)
  {
    typeChecker_.currentAction_ = name;
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
            typeChecker_.currentAction_ != null);
  }   
  
  protected void checkActionParaScope(String paraKind, Name name)
  {
    if (!isWithinActionParaScope())
    {
      Object[] params = { paraKind, name };
      error(term, ErrorMessage.INVALID_ACTION_PARA_SCOPE, params);      
    }
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
  
  /**
   * Overrides the old signature with type from pairs the new siganature
   * with the same name. TODO: ask Tim about name ids business
   */
  protected Signature overrideSignature(Signature oldSig, Signature newSig)
  {
    Signature result = factory().createSignature();
    List<NameTypePair> resultPairs = result.getNameTypePair();
    resultPairs.addAll(oldSig.getNameTypePair());        
    for(NameTypePair pair : newSig.getNameTypePair())
    {      
      GlobalDefs.namesEqual(pair.getName(), )
      pair.getZName().setId(null)
      if(!resultPairs.contains(pair))
      {
        resultPairs.add(pair);
      }
    }
    return result;
  }
  
  // do not clone LHS; adds RHS
  protected Signature joinSignature(Signature sigL, Signature sigR)
  {
    
  }
  
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
    for(NameTypePair pair : result)
    {            
      pair.setType(factory().createChannelType(pair.getType()));
    }
    return result;
  }

// TODO: code below still needs revision 
   
  /***********************************************************************
   * Syntax validation methods 
   **********************************************************************/        
    
  protected boolean isChannel(/*String name*/Name name)
  {
    boolean result = false;
    for (ChannelInfo channel : channels())
    {
      Name decl = channel.getChannelType().getDeclName();
      if (GlobalDefs.compareName(decl, name, true))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  // TODO: Check: why String at times and DeclName at other times?
  protected boolean isGenericChannel(Name name)
  {
    boolean result = false;
    for (ChannelInfo channel : channels())
    {
      Name decl = channel.getChannelType().getDeclName();
      if (GlobalDefs.compareName(decl, name, true))
      {
        if(channel.isGeneric())
        {
          result = true;
          break;
        }
      }
    }
    return result;
  }
  
  protected List<Name> getGenParamsChannel(Name name)
  {
    List<Name> result = new ArrayList<Name>();
    for (ChannelInfo channel : channels())
    {
      Name decl = channel.getChannelType().getDeclName();
      if (GlobalDefs.compareName(decl, name, true))
      {
        result = channel.getParams();
        break;
      }
    }
    return result;
  }
  
  protected boolean isProcess(Name name)
  {
    boolean result = false;
    for (ProcessInfo process : processes())
    {
      Name decl = process.getProcessName();
      if (GlobalDefs.compareName(decl, name, true))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  protected boolean isGenericProcess(Name name)
  {
    boolean result = false;
    for (ProcessInfo process : processes())
    {
      Name decl = process.getProcessName();
      if (GlobalDefs.compareName(decl, name, true))
      {
        if(process.isGeneric())
        {
          result = true;
          break;
        }
      }
    }
    return result;
  }
  
  protected boolean isChannelSet(/*Ref*/Name name)
  {
    boolean result = false;
    for (Name chanset : ZUtils.assertZNameList(chansets()))
    {
      if (ZUtils.assertZName(chanset).getWord().equals(
        ZUtils.assertZName(name).getWord()))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  // TODO: Check: why check getWord() at times but the whole object (with equals)
  //              at other times? Why not checking always with equals (to ignore strokes?)
  //              If that is okay, then it would avoid the ZDeclName casts and problems!
  //              If that is not okay, then either use ZDeclName/ZRefName as formal parameters
  //              or use DeclName and, while casting the object in the method code, either
  //              throw a particular exception (i.e. TypeCheckerException) or just allow the
  //              ClassCastException itself.
  //
  //              PS: Everywhere in CZT, apart from rewriting rule related tools, ZDeclName
  //                  is always used, so that is okay to cast in the typechecker to ZDeclName.
  //                  Other child classes for DeclName that is not ZDeclName, could be a
  //                  JokerDeclName used during term rewriting.
  protected boolean addChannel(Name name, Type type)
  {
    boolean result = true;
    for (ChannelInfo channel : channels())
    {
      if (channel.getChannelType().getDeclName().equals(name))
      {
        channel.getChannelType().setType(type);
        result = false;
      }
    }
    
    if(result)
    {
      NameTypePair nameType = factory().createNameTypePair(name, type);
      ChannelInfo insert = new ChannelInfo(nameType);
      channels().add(insert);
    }
    
    return result;
  }
  
  protected boolean addGenChannel(Name name, Type type, List<Name> params)
  {
    boolean result = true;
    for (ChannelInfo channel : channels())
    {
      if (channel.getChannelType().getDeclName().equals(name))
      {
        channel.getChannelType().setType(type);
        result = false;
      }
    }
    
    if(result)
    {
      NameTypePair nameType = factory().createNameTypePair(name, type);
      ChannelInfo insert = new ChannelInfo(nameType, true, params);
      channels().add(insert);
    }
    
    return result;
  }
  
  protected boolean addChannelSet(Name name)
  {    
    boolean result = !ZUtils.assertZNameList(chansets()).contains(name);
    if(result)
    {
      ZUtils.assertZNameList(chansets()).add(name);
    }    
    return result;
  }
   
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
  
  /**
   * Get the list of strokes to add for local variable declaration. 
   * That is, add a variable with each stroke in the list (x', x?, ...), 
   * rather than one variable with all strokes (x'?...).
   */
  protected ZStrokeList getCircusStrokeListForLocalVars()
  {
      ZStrokeList zsl = getFactory().getZFactory().createZStrokeList();
      zsl.add(getFactory().createNextStroke());
      zsl.add(getFactory().createInStroke());
      zsl.add(getFactory().createOutStroke());
      return zsl;
  }
  
  /**
   * Adds local variables to the process scope. That means
   * adding four new variables for each name type pair given.
   * For example, for (x, T), we add x, x', x?, x! with type T.
   * That is needed in order to put right variables into context
   * for various operations. See B.26 ExtractVars
   */
  protected List<NameTypePair> mkLocalVars(NameTypePair pair)
  {    
    // add the original variable name "x" to the scope
    List<NameTypePair> result = factory().list(pair);

    ZName varName = pair.getZName();
    Type varType  = pair.getType();

    ZStrokeList zsl = getCircusStrokeListForLocalVars();
    ZStrokeList strokeList = factory().createZStrokeList();
    for(Stroke stroke : zsl)
    { 
      // create new variable with unique ID, hence ZDeclName, combining 
      // its original strokes with the stroke to add here.
      strokeList.clear();        
      strokeList.addAll(pair.getZName().getStrokeList());
      strokeList.add(stroke);
      ZName strokedName = factory().createZDeclName(pair.getZName().getWord(), strokeList);        
      NameTypePair strokedPair = factory().createNameTypePair(strokedName, varType);        
      result.add(strokedPair);        
    }    
    assert (result.size() == zsl.size() + 1) :
      "Local variable declarations must add " + (zsl.size() + 1) + " variables into scope.";    
    
    // add them all into scope
    typeEnv().add(result);
    
    return result;
  }
  
  /**
   * Retrieves a type projection from a product type from the given offset (inclusive)
   * with the corresponding number of types. It obbeys the general Java invariant for
   * indexOf. To retrieve the remainder of the product type from an offset, just call
   * getProdTypeProjection(type, offset, size - offset).
   */
  protected static Type2 getProdTypeProjection(ProdType type, int offset, int count) 
  {
    List<Type2> innerTypes = factory().list(type.getType().subList(offset, count));
    assert !innerTypes.isEmpty() : "type projection resulted in an empty type.";
    
    Type2 result = innerTypes.size() > 1 ? 
      factory().createProdType(innerTypes) : innerTypes.get(0);
    
    return result;    
  }
  
  protected ProcessInfo getProcessInfo(Name name)
  {
    ProcessInfo result = null;
    List<ProcessInfo> processes = processes();
    for(ProcessInfo proc : processes)
    {
      if(proc.getProcessName().equals(name))
      {
        result = proc;
      }
    }
    return result;
  }
  
  protected String getKindOfProcess(Name name)
  {
    String result = "";
    for (ProcessInfo process : processes())
    {
      Name decl = process.getProcessName();
      if (GlobalDefs.compareName(decl, name, true))
      {
        result = process.getKindOfProcess().name();
        break;
      }
    }
    return result;
  }
  
  /**
   * Check whether the given local name is fresh within the current
   * local type environment scope.
   *
   * @param name the name to verify
   * @return true if local name is fresh, false otherwise
   */
  protected boolean isLocalNameFresh(Name name)
  {
    boolean result = true;    
    Type typeLocal = localCircTypeEnv().getType(ZUtils.assertZName(name));    
    if(!(typeLocal instanceof UnknownType))
    {
      result = false;
    }
    return result;
  }
  
  protected List<NameTypePair> getUsedChannels(Name procName)
  {
    List<NameTypePair> result = new ArrayList<NameTypePair>();
    for(ProcessInfo proc : processes())
    {
      if(proc.getProcessName().equals(procName))
      {
        result.addAll(proc.getUsedChans());
        break;
      }
    }
    return result;
  }
  
  protected List<Name> getGenParamsProcess(Name procName)
  {
    List<Name> result = new ArrayList<Name>();
    for(ProcessInfo proc : processes())
    {
      if(proc.getProcessName().equals(procName))
      {
        result = proc.getGenParams();
        break;
      }
    }
    return result;
  }
  
  public void addMuProcess(Name name)
  {
    muProcesses().add(name);
  }
  
  public void addMuAction(Name name)
  {
    muActions().add(name);
  }
  
  public void addAction4PostCheck(Name name)
  {
    actions4PostCheck().add(name);
  }
  
  public void removeMuProcess(Name name)
  {
    for(Name nameMuProc : muProcesses())
    {
      if(nameMuProc.equals(name))
      {
        muProcesses().remove(name);
        break;
      }
    }
  }
  
  public void removeMuAction(Name name)
  {
    for(Name nameMuAct : muActions())
    {
      if(nameMuAct.equals(name))
      {
        muActions().remove(name);
        break;
      }
    }
  }
  
  public void removeAction4PostCheck(Name name)
  {
    for(Name act : actions4PostCheck())
    {
      if(act.equals(name))
      {
        actions4PostCheck().remove(name);
        break;
      }
    }
  }
  
  public boolean isMuProcess(Name name)
  {
    boolean result = false;
    for(Name nameMuProc : muProcesses())
    {
      if(nameMuProc.equals(name))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  public boolean isMuAction(Name name)
  {
    boolean result = false;
    for(Name nameMuAct : muActions())
    {
      if(nameMuAct.equals(name))
      {
        result = true;
        break;
      }
    }
    return result;
  }
  
  public boolean isLovalVar(Name name)
  {
    boolean result = true;
    ZName zrn = ZUtils.assertZName(name);
    Type type = typeEnv().getType(zrn);
    if(!(type instanceof UnknownType))
    {
      ZName declName = factory().createZName(zrn.getWord());
      if(localCircTypeEnv().isAction(declName) || localCircTypeEnv().isNameSet(declName))
      {
        result = false;
      }
    }
    else
    {
      result = false;
    }
    return result;
  }
  
  public boolean isLocalVars(List<Name> names)
  {
    boolean result = true;
    for(Name name : names)
    {
      result = isLovalVar(name);
      if(!result)
      {
        break;
      }
    }
    return result;
  }
    
  //typecheck a file using an instance of this typechecker
  protected List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term, SectionInfo sectInfo)
  {
    return TypeCheckUtils.typecheck(termA, sectInfo, markup());
  }
  
  protected void error(Term term, ErrorMessage errorMsg, Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, errorMsg, params);
    error(term, errorAnn);
  }
  
  protected void error(Term term, ErrorMessage errorMsg, List<Object> params)
  {    
    error(term, errorMsg, params);
  }
  
  protected void error(Term term,
    net.sourceforge.czt.typecheck.z.ErrorMessage error,
    Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error.toString(), params);
    error(term, errorAnn);
  }
  
  protected ErrorAnn errorAnn(Term term, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
      sectName(), nearestLocAnn(term),
      markup());
    return errorAnn;
  }
  
  protected ErrorAnn errorAnn(Term term, String error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
      sectName(), nearestLocAnn(term),
      markup());
    return errorAnn;
  }
  
  //the local TypeEnv
  protected net.sourceforge.czt.typecheck.circus.util.TypeEnv circusTypeEnv()
  {
    return (net.sourceforge.czt.typecheck.circus.util.TypeEnv)typeChecker_.typeEnv_;
  }
  
  //add generic types from a list of Names to the TypeEnv
  protected void addGlobalGenParamTypes(List<Name> declNames)
  {
    //add each DeclName and its type
    List<String> names = new ArrayList<String>();
    for (Name declName : declNames)
    {
      ZName zdn = ZUtils.assertZDeclName(declName);
      GenParamType genParamType = factory().createGenParamType(zdn);
      PowerType powerType = factory().createPowerType(genParamType);
      
      //check if a generic parameter type is redeclared
      if (names.contains(zdn.getWord()))
      {
        Object [] params = {declName};
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
  
  protected void addProcessSignatureAnn(CircusProcess term, ProcessSignature psig)
  {
    assert false : "TODO";
    assert psig != null;
    ProcessSignatureAnn psigAnn = (ProcessSignatureAnn) term.getAnn(ProcessSignatureAnn.class);
    if (psigAnn == null) {
      psigAnn = factory().createProcessSignatureAnn(psigAnn);
      term.getAnns().add(psigAnn);
    }
    else {
      psigAnn.setProcessSignature(psig);
    }    
  }
  
  /** Adds a signature annotation create from a signature to a Term */
  protected void addActionSignatureAnn(CircusAction term, ActionSignature signature)
  {
    assert signature != null;
    ActionSignatureAnn signatureAnn =
      (ActionSignatureAnn) term.getAnn(ActionSignatureAnn.class);
    if (signatureAnn == null) {
      signatureAnn = factory().createActionSignatureAnn(signature);
      term.getAnns().add(signatureAnn);
    }
    else {
      ActionSignature oldSignature = signatureAnn.getActionSignature();
      assert false : "Check if this action signature has VariableSignatures within itself";
//      if (oldSignature instanceof VariableSignature &&
//          variableSignature(oldSignature).getValue() == oldSignature) {
//        variableSignature(oldSignature).setValue(signature);
//      }
//      else {
//        signatureAnn.setSignature(signature);
//      }
      signatureAnn.setActionSignature(signature);
    }
  }
  
  protected ProcessSignature joinProcessSignature(ProcessSignature procSigL, ProcessSignature procSigR)
  {
    
    ProcessSignature result = factory().createProcessSignature();
    BasicProcessSignature resultTemp = factory().createBasicProcessSignature();
    
    if(procSigL instanceof BasicProcessSignature)
    {
      BasicProcessSignature sigL = (BasicProcessSignature)procSigL;
      if(sigL.getActionsSignature() != null)
      {
        resultTemp.getActionsSignature().addAll(sigL.getActionsSignature());
      }
      if(sigL.getDeclNameSets() != null)
      {
        resultTemp.getDeclNameSets().addAll(sigL.getDeclNameSets());
      }
      if(sigL.getLocalZDeclsSignature() != null)
      {
        resultTemp.getLocalZDeclsSignature().addAll(sigL.getLocalZDeclsSignature());
      }
      if(sigL.getStateSignature() != null)
      {
        if(resultTemp.getStateSignature() != null)
        {
          List<NameTypePair> pairs = sigL.getStateSignature().getNameTypePair();
          List<NameTypePair> resultPairs = resultTemp.getStateSignature().getNameTypePair();
          for(NameTypePair pair : pairs)
          {
            if(!resultPairs.contains(pair))
            {
              resultPairs.add(pair);
            }
          }
          resultTemp.setStateSignature(factory().createSignature(resultPairs));
        }
        else
        {
          resultTemp.setStateSignature(sigL.getStateSignature());
        }
      }
      result = resultTemp;
    }
    
    if(procSigR instanceof BasicProcessSignature)
    {
      BasicProcessSignature sigR = (BasicProcessSignature)procSigR;
      if(sigR.getActionsSignature() != null)
      {
        resultTemp.getActionsSignature().addAll(sigR.getActionsSignature());
      }
      if(sigR.getDeclNameSets() != null)
      {
        resultTemp.getDeclNameSets().addAll(sigR.getDeclNameSets());
      }
      if(sigR.getLocalZDeclsSignature() != null)
      {
        resultTemp.getLocalZDeclsSignature().addAll(sigR.getLocalZDeclsSignature());
      }
      if(sigR.getStateSignature() != null)
      {
        if(resultTemp.getStateSignature() != null)
        {
          List<NameTypePair> pairs = sigR.getStateSignature().getNameTypePair();
          List<NameTypePair> resultPairs = resultTemp.getStateSignature().getNameTypePair();
          for(NameTypePair pair : pairs)
          {
            if(!resultPairs.contains(pair))
            {
              resultPairs.add(pair);
            }
          }
          resultTemp.setStateSignature(factory().createSignature(resultPairs));
        }
        else
        {
          resultTemp.setStateSignature(sigR.getStateSignature());
        }
      }
      result = resultTemp;
    }
    
    if(procSigL.getParamsOrIndexes() != null)
    {
      if(result.getParamsOrIndexes() != null)
      {
        List<NameTypePair> pairs = procSigL.getParamsOrIndexes().getNameTypePair();
        List<NameTypePair> resultPairs = result.getParamsOrIndexes().getNameTypePair();
        for(NameTypePair pair : pairs)
        {
          if(!resultPairs.contains(pair))
          {
            resultPairs.add(pair);
          }
        }
        result.setParamsOrIndexes(factory().createSignature(resultPairs));
      }
      else
      {
        result.setParamsOrIndexes(procSigL.getParamsOrIndexes());
      }
    }
    if(procSigR.getParamsOrIndexes() != null)
    {
      if(result.getParamsOrIndexes() != null)
      {
        List<NameTypePair> pairs = procSigR.getParamsOrIndexes().getNameTypePair();
        List<NameTypePair> resultPairs = result.getParamsOrIndexes().getNameTypePair();
        for(NameTypePair pair : pairs)
        {
          if(!resultPairs.contains(pair))
          {
            resultPairs.add(pair);
          }
        }
        result.setParamsOrIndexes(factory().createSignature(resultPairs));
      }
      else
      {
        result.setParamsOrIndexes(procSigR.getParamsOrIndexes());
      }
    }
    
    return result;
    
  }
    
  protected ActionSignature joinActionSignature(ActionSignature actionSigL, ActionSignature actionSigR)
  { 
    // at this point, names are ignored (i.e. must be null)
    assert actionSigL.getActionName() == null && 
           actionSigR.getActionName() == null : "cannot join signature with resolved names";
    
    // create new signnature with all info from LHS
    ActionSignature result = actionSigL.create(actionSigL.getChildren());
    
    // get the signature list structure
    ZSignatureList zslL = result.getZSignatureList();
    ZSignatureList zslR = actionSigR.getZSignatureList();    
    assert zslL.size() == zslR.size() : "ZSignatureList structure is invalid.";
    
    for(byte i = 0; i<zslL.size(); i++)
    {      
      Signature sL = zslL.get(i);
      Signature sR = zslR.get(i);
      zslL.set(i, joinSignature(sL, sR));
    }
    
    return result;
    
  }  
  
  // TODO: generalise this for Actions as well.
  // call this post check procedure after all paragraphs in a ZParaList had been checked.
  protected void postProcessCallCheck()
  {
    //post-check any previously unresolved calls within CircusProcesses
    List<Object> paraErrors = new ArrayList<Object>();
    for (Object next : paraErrors())
    {
      if (next instanceof CircusProcess)
      {
        CircusProcess proc = (CircusProcess) next;
        net.sourceforge.czt.typecheck.z.ErrorAnn errorAnn = proc.accept(postChecker());
        if (errorAnn != null)
        {
          paraErrors.add(errorAnn);
        }
      }
      else
      {
        paraErrors.add(next);
      }
    }
    paraErrors().clear();
    paraErrors().addAll(paraErrors);
    
    // Manuela commented this line, but gave no reason. It seems a mistake.
    errors().addAll(paraErrors);
  }
  
  /**
   * This implements Manuela's "NoRep" function (see B.52, p.136).
   * It is a stronger version of "z.Checker.checkForDuplicates", 
   * which would accept declarations like "x: \nat; x: \num" since 
   * both types would unify.
   */
  protected void checkForDuplicateNames(List<Name> declNames, ErrorMessage errorMsg)
  {
    checkForDuplicateNames(declNames, errorMsg.toString());
  }
  
  protected void checkForDuplicateNames(List<ZName> declNames, ErrorMessage errorMsg, Object... arguments)
  {
    Map<String, ZName> map = factory().hashMap();
    for (Iterator<ZName> iter = declNames.iterator(); iter.hasNext(); ) {
      ZName first = iter.next();
      String firstName = ZUtils.toStringZName(first);
      ZName second = map.get(firstName);
      if (second != null) {
        // check if the types don't match, raise an error 
        checkPair(first, second, termList, errorMessage);
        
        //merge the ids of the 2 names, and remove the duplicate
        factory().merge(second.getZName(), first.getZName());
        iter.remove();
      }
      map.put(firstName.intern(), first);
    }
  }
  
  protected void postActionCallCheck()
  {
    assert false : "TODO"; 
    List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> 
      paraErrors = postCheckParaErrors();
    paraErrors().clear();
    paraErrors().addAll(paraErrors);
  }
}
