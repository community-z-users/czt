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

import java.util.List;
import net.sourceforge.czt.circus.ast.ActionType;
import net.sourceforge.czt.circus.ast.ChannelSetType;
import net.sourceforge.czt.circus.ast.ChannelType;
import net.sourceforge.czt.circus.ast.CommunicationType;
import net.sourceforge.czt.circus.ast.NameSetType;
import net.sourceforge.czt.circus.ast.CircusSigType;
import net.sourceforge.czt.circus.ast.ProcessType;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.NameTypePair;
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
      // For well typed channel set expressions (e.g., CS \cup \lchanset e \rchanset)
      // we need to check that signatures do not contain variable types (e.g., generic
      // channel types have been resolved).
      //
      // Note also that, because we are only concern with two resolved channel set
      // types, this rules out cases like CS \cup \{ e \}. (TODO: check with more examples)
      //
      // Channel set typechecking reaches z.UnificationEnv, which takes care of
      // variable types, then go to the bottom of it using signature unification
      // in both directions to see all underlying types match. We need to override
      // that method here to make sure channel and name sets are treated accordingly.
      //
      // Same applies for NameSets
      result = unifyCircusMixedSigType(channelSetType(typeA), channelSetType(typeB), true);
    }
    else if (isNameSetType(typeA) && isNameSetType(typeB))
    {
      // TODO: this is not right... won't accept different types...
      result = unifyCircusMixedSigType(nameSetType(typeA), nameSetType(typeB), false);
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

  // used for Communication, and Mixed signatures (e.g., channel and name sets).
  // the former requires type unification, whereas the latter doesn't.
  protected UResult unifyCircusSigType(CircusSigType typeA, CircusSigType typeB)
  {
    return unify(typeA.getSignature(), typeB.getSignature());
  }

  // for channel and name set type checking when appearing in expressions
  // null = no; true = ChannelSet; false = NameSet
  private Boolean checkingCircusMixedSig_ = null;

  protected UResult unifyCircusMixedSigType(CircusSigType typeA, CircusSigType typeB, boolean isCS)
  {
    assert ((isCS && isChannelSetType(typeA) && isChannelSetType(typeB)) ||
            (!isCS && isNameSetType(typeA) && isNameSetType(typeB))) :
              "Only channel or name sets can have mixed type signatures";
    
    // null = no; true = ChannelSet; false = NameSet
    checkingCircusMixedSig_ = isCS;

    // we need to call the general signature unification because of
    // generic type resolution within channel and name sets.
    UResult result = unifyCircusSigType(typeA, typeB);

    checkingCircusMixedSig_ = null;
    return result;
  }
  
  protected UResult unifyResolvedSignature(Signature sigA, Signature sigB)
  {
    // try Z-unification first.
    UResult result = super.unifyResolvedSignature(sigA, sigB);

    // if we fail, then check for channel or name sets
    if (result == FAIL && checkingCircusMixedSig_ != null)
    {
      // we can safely assume channels within channel / name sets have been typechecked
      result = SUCC;

      // gather all elements from both signatures
      List<NameTypePair> combinedSig = factory_.list(sigA.getNameTypePair());
      combinedSig.addAll(sigB.getNameTypePair());

      // if we are checking for mixed signatures, the requirement is:
      //    * for channel sets: all elements are of ChannelType in both signatures
      //    * for name sets   : all elements are known to the state (?)
      if (checkingCircusMixedSig_)
      {
        for (NameTypePair pair : combinedSig)
        {
          // if all elements from both signatures have channel type, then we are okay
          if (!isChannelType(GlobalDefs.unwrapType(pair.getType())))
          {
            result = FAIL;
            break;
          }
        }
      }
      else
      {
        // well, for name sets, signatures will have types from state variables.
        // and we know if we get here that the right scopes are in place in the
        // typechecker. So, assume all is okay. TODO: check this (?)

        // do nothing, all is well... : type errors like name set elements that are unknown are caught elsewhere.
      }
    }
    // if we succeed, all is well: either it is a Z-case or that includes
    // channel set expressions that are simple (e.g., just reference expressions
    // in ChannelSetPara or in places where ChannelSet is needed, like hiding
    // or parallelism).
    //
    // if the result is partial, then it will be caught again at PostChecking.
    return result;
  }

  /**
   * Within signature verification of channel and name sets, we need to be
   * a bit more relaxed with the unification mechanism. That is, we allow
   * elements of different types within the same channel/name set, so long
   * as they all have ChannelSet or NameSet type. That is necessary since
   * channel and name sets do indeed mix ChannelSets/NameSets with elements
   * involving different types.
   *
   * MapA has a list of elements within the LHS signature, and the same for MapB.
   * For usual cases, we call the super that takes care of proper Z-like unification.
   * For Circus special cases, we only care that the right structure is being unified.
   * That is, all the elements in the map are channel sets / name sets, respectively.
   *
   * Note that this is a one-way check. That is, check all elements of mapA wrt
   * mapB. The upper-level (unifySignature) makes sure the other way round is
   * also checked by calling mapA with mapB. That is, the code here does not need
   * to iterate over mapB.
   *
   * @param mapA
   * @param mapB
   * @return
   */
//
//  protected UResult unifySignatureAux(Map<String, NameTypePair> mapA,
//                                      Map<String, NameTypePair> mapB)
//  {
//    // try Z-unification first.
//    UResult result = super.unifySignatureAux(mapA, mapB);
//
//    // if we fail, then check for channel or name sets
//    if (result == FAIL)
//    {
//      boolean consistent = true;
//      // if mapA has only channel / nametyped values or
//      for(NameTypePair ntp : mapA.values())
//      {
//        //isChannelSetType(ntp.getType());
//
//      }
//    }
//    // if we succeed, all is well: either it is a Z-case or that includes
//    // channel set expressions that are simple (e.g., just reference expressions
//    // in ChannelSetPara or in places where ChannelSet is needed, like hiding
//    // or parallelism).
//    //
//    // if the result is partial, then it will be caught again at PostChecking.
//    return result;
//}
}
