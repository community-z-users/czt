package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for PowerType that hides VariableType instances
 * if they have a value.
 */
public class PowerTypeImpl
  extends Type2Impl
  implements PowerType
{
  protected PowerTypeImpl(PowerType powerType)
  {
    super(powerType);
  }

  public void setType(Type2 type)
  {
    PowerType powerType = (PowerType) term_;
    powerType.setType(type);
  }

  public Type2 getType()
  {
    PowerType powerType = (PowerType) term_;
    Type2 result = powerType.getType();
    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;
      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }

  public String toString()
  {
    PowerType powerType = (PowerType) term_;
    return powerType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof PowerType) {
      PowerType powerType = (PowerType) obj;
      return getType().equals(powerType.getType());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "PowerTypeImpl".hashCode();
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}
