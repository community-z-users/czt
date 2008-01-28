/*
 * Factory.java
 *
 * Created on 17 de Junho de 2005, 17:28
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.typecheck.circus.impl;

import java.util.List;
import net.sourceforge.czt.circus.ast.ActionSignature;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.BasicChannelSetExpr;
import net.sourceforge.czt.circus.ast.BasicProcessSignature;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CircusChannelSet;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.CircusNameSet;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.CommunicationList;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.circus.util.CircusString;
import net.sourceforge.czt.circus.util.CircusUtils;
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

/**
 *
 * @author Manuela
 */
public class Factory 
  extends net.sourceforge.czt.typecheck.z.impl.Factory
{
  /** The CircusToolsFactory that is used to create wrapped types. */
  protected CircusFactory circusFactory_;
    
  public Factory()
  {
    super();
    init(new CircusFactoryImpl());     
  }

  public Factory(ZFactory zFactory)
  {
    super(zFactory);
    init(new CircusFactoryImpl());     
  }

  public Factory(ZFactory zFactory, CircusFactory circusFactory)
  {
    super(zFactory);
    init(circusFactory);         
  }
  
  private void init(CircusFactory circusFactory)
  {
    //zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    circusFactory_ = circusFactory;
    
    //creates a synchronisation channel and transformer paragraph type names with ID.    
    //i.e., all ZNames in CircusUtils MUST be initialised here ;-)
    overwriteNameID(CircusUtils.SYNCH_CHANNEL_TYPE_NAME);
    overwriteNameID(CircusUtils.TRANSFORMER_TYPE_NAME);   
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

  public ProcessSignature createEmptyCircusProcessSignature()
  {
    return circusFactory_.createEmptyCircusProcessSignature();
  }
  
  public BasicProcessSignature createEmptyBasicProcessSignature()
  {
    return circusFactory_.createEmptyBasicProcessSignature();
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
  
  public ActionSignature createActionSignature(Name actionName,
    Signature formals, Signature usedNameSets, CommunicationList commList)
  {
    return circusFactory_.createActionSignature(actionName, formals, usedNameSets, commList);
  }  
  
  public ActionSignature createEmptyActionSignature()
  {
    return circusFactory_.createEmptyActionSignature();
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
    assert false : "TODO: resolve generics";
    ChannelSetType chanSetType = circusFactory_.createChannelSetType();
    Signature channelsSig = circusFactory_.createSignature();
    chanSetType.setSignature(channelsSig);    
    return chanSetType;
  }

  public ChannelSetType createChannelSetType(Name name, Signature channelsSig)
  {
    assert false : "TODO: resolve generics";    
    ChannelSetType chanSetType = circusFactory_.createChannelSetType(name, channelsSig);    
    return chanSetType;
  }
  
  public NameSetType createNameSetType()
  {
    NameSetType nameSetType = circusFactory_.createNameSetType();
    Signature namesSig = circusFactory_.createSignature();
    nameSetType.setSignature(namesSig);    
    return nameSetType;
  }

  public NameSetType createNameSetType(Name name, Signature namesSig)
  {
    NameSetType nameSetType = circusFactory_.createNameSetType(name, namesSig);    
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
  
  public ZName createTransformerName()
  {
    return CircusUtils.TRANSFORMER_TYPE_NAME;
  }  
  
  public PowerType createSynchType()
  {           
    return CircusUtils.SYNCH_CHANNEL_TYPE;
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
}
