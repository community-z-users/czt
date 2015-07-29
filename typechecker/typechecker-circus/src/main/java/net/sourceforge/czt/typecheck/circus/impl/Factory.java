/*
Copyright (C) 2007 Leo Freitas
This file is part of the CZT project.
The CZT project contains free software;
you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.
The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.
You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.typecheck.circus.impl;

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionSignatureList;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.BasicChannelSetExpr;
import net.sourceforge.czt.circus.ast.ChannelSetList;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusChannelSet;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.CircusNameSet;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.CommunicationList;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.ast.NameSetList;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessSignatureList;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.CallUsage;
import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.ast.StateUpdate;
import net.sourceforge.czt.circus.ast.ZSignatureList;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.circus.util.CircusUtils;
import net.sourceforge.czt.typecheck.z.impl.VariableSignature;
import net.sourceforge.czt.typecheck.z.impl.VariableType;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.impl.ZFactoryImpl;

/**
 *
 * @author Leo Freitas
 */
public class Factory 
  extends net.sourceforge.czt.typecheck.z.impl.Factory
{
  
  /** The CircusToolsFactory that is used to create wrapped types. */
  protected CircusFactory circusFactory_;
    
  public Factory()
  {
    this(new ZFactoryImpl(), new CircusFactoryImpl());
  }

  public Factory(ZFactory zFactory)
  {
    this(zFactory, new CircusFactoryImpl());    
  }

  public Factory(ZFactory zFactory, CircusFactory circusFactory)
  {
    // use the circus.util.Factory to create Z objects ;-)
    super(zFactory, new net.sourceforge.czt.circus.util.Factory(circusFactory));
    init(circusFactory);         
  }
  
  private void init(CircusFactory circusFactory)
  {
    //zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    circusFactory_ = circusFactory;
    
    //creates a synchronisation channel and transformer paragraph type names with ID.    
    //i.e., all ZNames in CircusUtils MUST be initialised here ;-)
    overwriteNameID(CircusUtils.SYNCH_CHANNEL_TYPE_NAME);
    overwriteNameID(CircusUtils.CIRCUS_ID_TYPE_NAME);
    overwriteNameID(CircusUtils.TRANSFORMER_TYPE_NAME);   
  }
  
  /**
   * For now, overrides the deep clonning of terms and just use
   * shallow, term.create(term.getChildren()) cloning. 
   * @param term
   * @return
   */
  @SuppressWarnings("unchecked")
public <T extends Term> T deepCloneTerm(T term)
  {    
    return (T)Factory.cloneTerm(term);
  }
  
  @SuppressWarnings("unchecked")
public <T extends Term> T shallowCloneTerm(T term)
  {
    return (T)term.create(term.getChildren());
  }
  
  private static int freshId_ = 0;
  
  private static synchronized void incrementFreshId()
  {
	  freshId_++;
	  
  }
  public String createFreshName(String prefix)
  {
    String result = prefix + freshId_;
    incrementFreshId();
    return result;
  }

  public CircusFactory getCircusFactory()
  {
    return circusFactory_;
  }

  public CircusChannelSet createCircusChannelSet(Expr expr)
  {
    CircusChannelSet result = circusFactory_.createCircusChannelSet(expr);
    return result;
  }

  public BasicChannelSetExpr createBasicChannelSet(List<Communication> comms)
  {
    BasicChannelSetExpr result = circusFactory_.createBasicChannelSetExpr(
      circusFactory_.createCircusCommunicationList(comms));
    return result;
  }
 
  public CircusNameSet createCircusNameSet(Expr expr)
  {
    CircusNameSet result = circusFactory_.createCircusNameSet(expr);
    return result;
  }

  public ProcessSignature createEmptyProcessSignature()
  {
    return circusFactory_.createEmptyProcessSignature();
  }
  
  public ProcessSignature createProcessSignature(
    Name name, ZNameList genFormals, Signature paramOrIndexes,
    ProcessSignatureList processSignatures, CallUsage usage)
  {
    return circusFactory_.createProcessSignature(name, genFormals, paramOrIndexes, processSignatures, usage);
  }
  
  public ProcessSignature createCompleteProcessSignature(Name name, 
    ZNameList genFormals, Signature paramOrIndexes, Signature stateSignature,
    ProcessSignatureList processSignatures, ActionSignatureList actionSignatures,
    ZSignatureList basicProcessLocalZSignatures, ChannelSetList parallelProcessChannelSets,
    StateUpdate stateUpdate, CallUsage usage)
  {
    return circusFactory_.createCompleteProcessSignature(name, 
      genFormals, paramOrIndexes, stateSignature, processSignatures, 
      actionSignatures, basicProcessLocalZSignatures, parallelProcessChannelSets,
      stateUpdate, usage);
  }
  
  public ProcessSignature createParamProcessSignature(Signature paramOrIndexes,
    ProcessSignatureList processSignatures, CallUsage usage)
  {
    return createProcessSignature(null, circusFactory_.createZNameList(), 
      paramOrIndexes, processSignatures, usage);    
  }
  
  public ProcessSignatureList createProcessSignatureList()
  {
    return circusFactory_.createProcessSignatureList();
  }
  
  public ProcessSignatureList createProcessSignatureList(List<? extends ProcessSignature> list)
  {
    return circusFactory_.createProcessSignatureList(list);
  }
  
//  public ProcessType createProcessType()
//  {    
//    return createProcessType(createEmptyProcessSignature());
//  }

  public ProcessType createProcessType(ProcessSignature procSig)
  {
    ProcessType processType = circusFactory_.createProcessType(procSig);    
    return processType;
  }
  
  public ActionSignature createCompleteActionSignature(
    Name actionName, Signature formals, Signature localVars,
    Signature usedChannels, CommunicationList usedComms,
    ChannelSetList usedChannelSets, NameSetList usedNameSets)
  {
    return circusFactory_.createCompleteActionSignature(actionName, 
      formals, localVars, usedChannels, usedComms, usedChannelSets,
      usedNameSets);
  }
  
  public ActionSignature createActionSignature(Name actionName,
    Signature formals, Signature localVars, Signature usedChannels, 
    CommunicationList commList)
  {
    return createActionSignature(actionName, formals, localVars, 
      usedChannels, commList, circusFactory_.createCircusChannelSetList(),
      circusFactory_.createCircusNameSetList());
  }  
  
  public ActionSignature createActionSignature(Name actionName,
    Signature formals, Signature localVars, Signature usedChannels, 
    CommunicationList commList, ChannelSetList usedChannelSets, NameSetList usedNameSets)
  {
    return circusFactory_.createActionSignature(actionName, formals, 
      localVars, usedChannels, commList, usedChannelSets, usedNameSets);
  }  

  public ActionSignature createEmptyActionSignature()
  {
    return circusFactory_.createEmptyActionSignature();
  }
  
  public ActionSignature createInitialMuActionSignature(Name actionName)
  {
    return circusFactory_.createInitialMuActionSignature(actionName);                          
  }
  
  public ActionType createActionType()
  {    
    return createActionType(createEmptyActionSignature());
  }

  public ActionType createActionType(ActionSignature actionSig)
  {
    ActionType actionType = circusFactory_.createActionType(actionSig);
    return actionType;
  }

  public ChannelSetType createChannelSetType()
  {
    return createChannelSetType(createVariableSignature());
  }
  
  public ChannelSetType createChannelSetType(Signature csSig)
  { 
    ChannelSetType channelSetType = circusFactory_.createChannelSetType(csSig);    
    return channelSetType;
  }
  
  public NameSetType createNameSetType()
  {     
    return createNameSetType(createVariableSignature());
  }

  public NameSetType createNameSetType(Signature namesSig)
  { 
    NameSetType nameSetType = circusFactory_.createNameSetType(namesSig);    
    return nameSetType;
  }

  /**
   * This is a channel type that has an ALPHA variable type within it.
   */
  public ChannelType createChannelType()
  {
    //assert false : "TODO: resolve generics";
    // create an underlying variable type as the channel type
    // that means type inference hasn't been done yet.
    VariableType vType = createVariableType();
    ChannelType result = createChannelType(vType);
    return result;    
  }

  //TODO: Check how the generics business will be solved. Maybe the inner type should be Type (rather than Type2)?
  public ChannelType createChannelType(Type2 type)
  {        
    // innermost corejava AST-impl type with underlying type.
    ChannelType channelType = circusFactory_.createChannelType(type);
    
    // outermost typechecker AST-impl type potentially with variable types.
    ChannelType result = new ChannelTypeImpl(channelType);
    return result;
  }
  
  public CommunicationType createCommunicationType()
  {
    //assert false : "TODO: resolve generics";
    // create an underlying variable type as the channel type
    // that means type inference hasn't been done yet.
    VariableSignature vSig = createVariableSignature();
    CommunicationType result = createCommunicationType(vSig);
    return result;    
  }
  
  public CommunicationType createCommunicationType(Signature signature)
  {
    // innermost corejava AST-impl type with underlying type.
    CommunicationType commType = circusFactory_.createCommunicationType();
    
    // outermost typechecker AST-impl type potentially with variable types.
    CommunicationType result = new CommunicationTypeImpl(commType);
    return result;
  }
  
  /*public ProcessAnn createProcessAnn(ProcessType type)
  {
    ProcessAnn processAnn = circusFactory_.createProcessAnn(type);
    //ProcessAnn result = new ProcessAnnImpl(type);
    return processAnn;
  }

  public ActionAnn createActionAnn(ActionType type)
  {
    ActionAnn actionAnn = circusFactory_.createActionAnn(type);
    //ActionAnn result = new ActionAnnImpl(actionAnn);
    return actionAnn;
  }*/
  
  public SchExprAction createSchExprAction(Expr expr) 
  {
    return circusFactory_.createSchExprAction(expr);
  }
  
  public ZNameList createZNameList() {
      return zFactory_.createZNameList();
  }
  
  public ZName createSynchName()
  {
    return CircusUtils.SYNCH_CHANNEL_TYPE_NAME;
  }
  
  public ZName createCircusIdName()
  {
    return CircusUtils.CIRCUS_ID_TYPE_NAME;
  }
  
  public ZName createTransformerName()
  {
    return CircusUtils.TRANSFORMER_TYPE_NAME;
  }  
  
  public PowerType createSynchType()
  {           
    return CircusUtils.SYNCH_CHANNEL_TYPE;
  }
  
  public PowerType createCircusIdType()
  {           
    return CircusUtils.CIRCUS_ID_TYPE;
  }
  
  public PowerType createTransformerType()
  {           
    return CircusUtils.TRANSFORMER_TYPE;
  }
  
  public Signature createSignature(NameTypePair pair)
  {
    Signature result = createSignature(list(pair));
    return result;
  }
  
  public NameSetType createEmptyNameSetType()
  {
    return createNameSetType(createSignature());
  }
  
  public CircusCommunicationList createCircusCommunicationList(List<Communication> comms)
  {
    return circusFactory_.createCircusCommunicationList(comms);
  }
  
  public CircusCommunicationList createCircusCommunicationList(Communication comm)
  {
    return circusFactory_.createCircusCommunicationList(list(comm));
  }
  
  public CircusCommunicationList createEmptyCircusCommunicationList()
  {  
    return circusFactory_.createCircusCommunicationList();
  }
}
