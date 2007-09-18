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
 * @author Manuela
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
    if (isActionType(typeA) && isSchemaType(typeB))
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
    else if (isActionType(typeA) && isActionType(typeB))
    {
      result = unifyActionType(actionType(typeA), actionType(typeB));
    }
    else
      result = super.unify(typeA, typeB);
    return result;
  }
  
  public boolean isActionType(Type2 type)
  {
    return (type instanceof ActionType);
  }
  
  public ActionType actionType(Type2 type)
  {
    return (ActionType)type;
  }
  
  protected UResult unifyActionType(ActionType typeA, ActionType typeB)
  {
    Signature sigA = typeA.getActionSignature().getLocalVars();
    Signature sigB = typeB.getActionSignature().getLocalVars();
    UResult result = unifySignature(sigA, sigB);
    if (result == SUCC)
    {
      sigA = typeA.getActionSignature().getFormalParams();
      sigB = typeB.getActionSignature().getFormalParams();
      result = unifySignature(sigA, sigB);
    }
    return result;
  }
}
