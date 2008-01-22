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
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.ProcessSignature;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.impl.CircusFactoryImpl;
import net.sourceforge.czt.circus.util.CircusString;
import net.sourceforge.czt.typecheck.z.impl.VariableType;
import net.sourceforge.czt.z.ast.Expr;
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
  
  private final ZName synchNameWithID_;

  public Factory()
  {
    super();
    //zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    circusFactory_ = new CircusFactoryImpl();
    //creates a SYNCH_CHANNEL NAME with ID.
    synchNameWithID_ = createZDeclName(CircusString.CIRCUSSYNCH);
  }

  public Factory(ZFactory zFactory)
  {
    super(zFactory);
    //zFactory_ = zFactory;
    circusFactory_ = new CircusFactoryImpl();
  }

  public Factory(ZFactory zFactory, CircusFactory circusFactory)
  {
    super(zFactory);
    //zFactory_ = zFactory;
    circusFactory_ = circusFactory;
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
    BasicChannelSetExpr result = circusFactory_.createBasicChannelSetExpr(comms);
    return result;
  }
 
  public CircusNameSet createCircusNameSet(Expr expr)
  {
    CircusNameSet result = circusFactory_.createCircusNameSet(expr);
    return result;
  }

  public ProcessSignature createProcessSignature()
  {
    return circusFactory_.createProcessSignature();
  }
  
  public BasicProcessSignature createBasicProcessSignature()
  {
    return circusFactory_.createBasicProcessSignature();
  }

  public ProcessType createProcessType()
  {    
    return createProcessType(circusFactory_.createProcessSignature());
  }

  public ProcessType createProcessType(ProcessSignature procSig)
  {
    ProcessType processType = circusFactory_.createProcessType(procSig);    
    return processType;
  }
  
  public ActionSignature createActionSignature()
  {
    return circusFactory_.createActionSignature();
  }
  
  public ActionType createActionType()
  {    
    return createActionType(circusFactory_.createActionSignature());
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

  public ChannelSetType createChannelSetType(Signature channelsSig)
  {
    assert false : "TODO: resolve generics";    
    ChannelSetType chanSetType = circusFactory_.createChannelSetType(channelsSig);    
    return chanSetType;
  }
  
  public NameSetType createNameSetType()
  {
    NameSetType nameSetType = circusFactory_.createNameSetType();
    Signature namesSig = circusFactory_.createSignature();
    nameSetType.setSignature(namesSig);    
    return nameSetType;
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
    assert false : "TODO: resolve generics";
    // create an underlying variable type as the channel type
    // that means type inference hasn't been done yet.
    VariableType vType = createVariableType();
    ChannelType result = createChannelType(vType);
    return result;    
  }

  public ChannelType createChannelType(Type2 type)
  {    
    assert false : "TODO: resolve generics";    
    
    // innermost corejava AST-impl type with underlying type.
    ChannelType channelType = factory_.createChannelType(type);
    
    // outermost typechecker AST-impl type potentially with variable types.
    ChanneltType result = new ChannelTypeImpl(channelType);
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
    return synchNameWithID_;
  }
  
  public PowerType createSynchType()
  {       
    PowerType result = createPowerType(createGivenType(createSynchName()));
    return result;
  }
  
  public Signature createSignature(NameTypePair pair)
  {
    Signature result = createSignature(list(pair));
    return result;
  }
}
