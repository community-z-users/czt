/*
 * UnificationEnv.java
 *
 * Created on 17 de Junho de 2005, 17:33
 *
 * To change this template, choose Tools | Options and locate the template under
 * the Source Creation and Management node. Right-click the template and choose
 * Open. You can then make changes to the template in the Source Editor.
 */

package net.sourceforge.czt.typecheck.circus.util;

import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.CircusSigType;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type2;

//import net.sourceforge.czt.z.ast.*;
//import net.sourceforge.czt.typecheck.z.util.*;
//import net.sourceforge.czt.typecheck.z.impl.*;
//import net.sourceforge.czt.circus.ast.*;
//import net.sourceforge.czt.typecheck.circus.impl.*;
//
/**
 *
 * @author Leo
 */
public class UnificationEnv
  extends net.sourceforge.czt.typecheck.z.util.UnificationEnv
{
  
  public UnificationEnv()
  {
    super();
  }
  
  public UnificationEnv(net.sourceforge.czt.typecheck.z.impl.Factory zFactory)
  {
    super(zFactory);
  }
  
  public UResult unify(Type2 typeA, Type2 typeB)
  {
    UResult result = FAIL;
    if (isProcessType(typeA) && isProcessType(typeB))
    {
      result = unifyProcessType(processType(typeA), processType(typeB));
    }
    else if (isActionType(typeA) && isActionType(typeB))
    {
      result = unifyActionType(actionType(typeA), actionType(typeB));
    }
    else if (isActionType(typeA) && isSchemaType(typeB))
    {
      result = unifySignature(actionType(typeA).getActionSignature().getLocalVars(),
        schemaType(typeB).getSignature());
    }
    else if (isActionType(typeB) && isSchemaType(typeA))
    {
      result = unifySignature(actionType(typeB).getActionSignature().getLocalVars(),
        schemaType(typeA).getSignature());
    }
    else if (isActionType(typeA) && isPowerType(typeB) && isSchemaType(powerType(typeB).getType()))
    {
      result = unifySignature(actionType(typeA).getActionSignature().getLocalVars(),
        schemaType(powerType(typeB).getType()).getSignature());
    }
    else if (isActionType(typeB) && isPowerType(typeA) && isSchemaType(powerType(typeA).getType()))
    {
      result = unifySignature(actionType(typeB).getActionSignature().getLocalVars(),
        schemaType(powerType(typeA).getType()).getSignature());
    }
    else if (isChannelType(typeA) && isChannelType(typeB))
    {
      result = unifyChannelType(channelType(typeA), channelType(typeB));
    }
    else if (isCommunicationType(typeA) && isCommunicationType(typeB))
    {
      result = unifyCircusSigType(communicationType(typeA), communicationType(typeB));
    }
    else if (isChannelSetType(typeA) && isChannelSetType(typeB))
    {
      result = unifyCircusSigType(channelSetType(typeA), channelSetType(typeB));
    }
    else if (isNameSetType(typeA) && isNameSetType(typeB))
    {
      result = unifyCircusSigType(nameSetType(typeA), nameSetType(typeB));
    }
    else
      result = super.unify(typeA, typeB);
    return result;
  }
  
  public boolean isProcessType(Type2 type)
  {
    return (type instanceof ProcessType);
  }
  
  public ProcessType processType(Type2 type)
  {
    return (ProcessType)type;
  }
  
  public boolean isActionType(Type2 type)
  {
    return (type instanceof ActionType);
  }
  
  public ActionType actionType(Type2 type)
  {
    return (ActionType)type;
  }
  
  public boolean isChannelType(Type2 type)
  {
    return (type instanceof ChannelType);
  }
  
  public ChannelType channelType(Type2 type)
  {
    return (ChannelType)type;
  }
  
  public boolean isCommunicationType(Type2 type)
  {
    return (type instanceof CommunicationType);
  }
  
  public CommunicationType communicationType(Type2 type)
  {
    return (CommunicationType)type;
  }
  
  public boolean isChannelSetType(Type2 type)
  {
    return (type instanceof ChannelSetType);
  }
  
  public ChannelSetType channelSetType(Type2 type)
  {
    return (ChannelSetType)type;
  }
  
  public boolean isNameSetType(Type2 type)
  {
    return (type instanceof NameSetType);
  }
  
  public NameSetType nameSetType(Type2 type)
  {
    return (NameSetType)type;
  }
  
  protected UResult unifyProcessType(ProcessType typeA, ProcessType typeB)
  {
    Signature sigA = typeA.getProcessSignature().getFormalParamsOrIndexes();
    Signature sigB = typeB.getProcessSignature().getFormalParamsOrIndexes();
    UResult result = unifySignature(sigA, sigB);
    if (result == SUCC)
    {
      //TODO: CHECK: do we need to worry about GenFormals here?
      //sigA = typeA.getProcessSignature().getGenFormals();
      //sigB = typeB.getProcessSignature().getGenFormals();
      result = unifySignature(sigA, sigB);
    }
    assert false : "TODO";
    return result;    
  }
  
  protected UResult unifyActionType(ActionType typeA, ActionType typeB)
  {
    Signature sigA = typeA.getActionSignature().getFormalParams();
    Signature sigB = typeB.getActionSignature().getFormalParams();
    UResult result = unifySignature(sigA, sigB);
    if (result == SUCC)
    {
      sigA = typeA.getActionSignature().getLocalVars();
      sigB = typeB.getActionSignature().getLocalVars();
      result = unifySignature(sigA, sigB);
    }
    return result;
  }
  
  protected UResult unifyChannelType(ChannelType typeA, ChannelType typeB)
  {
    return unify(typeA.getType(), typeB.getType());    
  }
  
  protected UResult unifyCircusSigType(CircusSigType typeA, CircusSigType typeB)
  {
    return unify(typeA.getSignature(), typeB.getSignature());    
  }
}
