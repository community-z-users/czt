package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.PowerTypeImpl;

/**
 * An implementation for PowerType that hides VariableType instances
 * if they have a value.
 */
public class VPowerTypeImpl
  extends PowerTypeImpl
{
  protected VPowerTypeImpl()
  {
    super();
  }

  public Type2 getType()
  {
    Type2 result = super.getType();

    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;

      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }
}
