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
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusProcess;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.typecheck.circus.impl.ChannelInfo;
import net.sourceforge.czt.typecheck.circus.impl.ProcessInfo;
import net.sourceforge.czt.typecheck.circus.util.GlobalDefs;
import net.sourceforge.czt.typecheck.circus.util.LocalTypeEnv;
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
  
  public void setCircusFormalParametersDecl(boolean val)
  {
    typeChecker_.circusFormalParameters_ = val;
  }
  
  public boolean isCheckingCircusFormalParamDecl()
  {
    return typeChecker_.circusFormalParameters_;
  }  
  
  protected net.sourceforge.czt.typecheck.circus.impl.Factory factory()
  {
    return typeChecker_.getFactory();
  }
  
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
    return typeChecker_.communicChecker_;
  }
  
  protected Checker<ProcessSignature> processChecker()
  {
    return typeChecker_.processChecker_;
  }
  
  protected Checker<Boolean> channelDeclChecker()
  {
    return typeChecker_.channelDeclChecker_;
  }
  
  protected Checker<NameList> channelsUsedChecker()
  {
    return typeChecker_.channelsUsedChecker_;
  }
  
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
   * This variables control process scoping. That is, one cannot have
   * nested process declarations.
   */
  protected boolean isWithinProcessParaScope()
  {
    return typeChecker_.currentProcess_ != null;
  }
    
  
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
  
  protected void setOnTheFlyProcesses(ZParaList procs)
  {
    typeChecker_.onTheFlyProcesses_= procs;
  }
  
  protected ZParaList onTheFlyProcesses()
  {
    return typeChecker_.onTheFlyProcesses_;
  }
  
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
 
  protected void addVars(List<NameTypePair> vars)
  {
    for(NameTypePair var : vars)
    {
      typeEnv().add(var);
      /* TODO: Check: Shouldn't it be:
      Name primedVar = factory().createZDeclName(var.getZDeclName().getWord(), Arrays.asList(factory().createNextStroke()), null);
       */
      ZName primedVar = factory().createZName(var.getZName().getWord() + ZString.PRIME, null, null);
      typeEnv().add(primedVar, var.getType());
    }
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
  
  protected Type getChannelType(Name name)
  {
    Type result = null;
    for(ChannelInfo chan : channels())
    {
      if(GlobalDefs.compareName(name, chan.getChannelType().getDeclName(), true))
      {
        result = chan.getChannelType().getType();
        break;
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
   * Método que verifica se o nome passado como parâmetro é
   * um nome local novo.
   * @param name  o nome a verificar
   * @return true caso o nome seja novo (localmente)
   *         false, caso contrário.
   */
  protected boolean isNewDef(Name name)
  {
    boolean result = true;
    ZName refName = factory().createZName(ZUtils.assertZName(name));
    Type typeLocal = typeEnv().getType(refName);
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
  
  protected void error(Term term, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(term, error, params);
    error(term, errorAnn);
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
  protected LocalTypeEnv localCircTypeEnv()
  {
    return typeChecker_.localCircTypeEnv_;
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
  
  protected void addActionSignatureAnn(CircusAction term, ActionSignature asig)
  {
    assert asig != null;
    ActionSignatureAnn psigAnn = (ActionSignatureAnn) term.getAnn(ActionSignatureAnn.class);
    if (asigAnn == null) {
      asigAnn = factory().createActionSignatureAnn(asigAnn);
      term.getAnns().add(asigAnn);
    }
    else {
      asigAnn.setActionSignature(asig);
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
    
    ActionSignature result = factory().createActionSignature();
    
    if(actionSigL.getLocalVarsSignature() != null)
    {
      result.setLocalVarsSignature(actionSigL.getLocalVarsSignature());
    }
    if(actionSigR.getLocalVarsSignature() != null)
    {
      if(result.getLocalVarsSignature() != null)
      {
        List<NameTypePair> pairs = actionSigR.getLocalVarsSignature().getNameTypePair();
        List<NameTypePair> resultPairs = result.getLocalVarsSignature().getNameTypePair();
        for(NameTypePair pair : pairs)
        {
          if(!resultPairs.contains(pair))
          {
            resultPairs.add(pair);
          }
        }
        result.setLocalVarsSignature(factory().createSignature(resultPairs));
      }
      else
      {
        result.setLocalVarsSignature(actionSigR.getLocalVarsSignature());
      }
    }
    if(actionSigL.getParams() != null)
    {
      result.setParams(actionSigL.getParams());
    }
    if(actionSigR.getParams() != null)
    {
      if(result.getParams() != null)
      {
        List<NameTypePair> pairs = actionSigR.getParams().getNameTypePair();
        List<NameTypePair> resultPairs = result.getParams().getNameTypePair();
        for(NameTypePair pair : pairs)
        {
          if(!resultPairs.contains(pair))
          {
            resultPairs.add(pair);
          }
        }
        result.setLocalVarsSignature(factory().createSignature(resultPairs));
      }
      else
      {
        result.setParams(actionSigR.getParams());
      }
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
  protected boolean hasDuplicatedNames(List<Name> declNames)
  {
    Set<Name> set = factory().hashSet();
    set.adddAll(declNames);
    return (set.size() = declNames.size());
  }
  
  protected void checkForDuplicateNames(List<Name> declNames, ErrorMessage errorMsg)
  {
    checkForDuplicateNames(declNames, errorMsg.toString());
  }
  
  protected void checkForDuplicateNames(List<Name> declNames, String errorMsg)
  {
    if (hasDuplicatedNames(declNames))
    {
      assert !declNames.isEmpty() : "Duplicated list of names cannot be empty.";
      
      Object [] params = {declNames.toString()};
      // at the pair.getName() location
      error(declNames.get(0), errorMsg, params);  
    }
  }
  
  protected void postActionCallCheck()
  {
    List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> 
      paraErrors = postCheckParaErrors();
    paraErrors().clear();
    paraErrors().addAll(paraErrors);
  }
}
