package net.sourceforge.czt.typecheck.util.impl;

import java.util.List;

import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for GenericType that hides VariableType instances
 * if they have a value.
 */
public class GenericTypeImpl
  extends TypeImpl
  implements GenericType
{
  protected GenericTypeImpl(GenericType genericType)
  {
    super(genericType);
  }

  public net.sourceforge.czt.base.ast.ListTerm getName()
  {
    GenericType genericType = (GenericType) term_;
    return genericType.getName();
  }

  public Type2 getType()
  {
    GenericType genericType = (GenericType) term_;
    return genericType.getType();
  }

  public void setType(Type2 type)
  {
    GenericType genericType = (GenericType) term_;
    genericType.setType(type);
  }

  public void setOptionalType(Type2 optionalType)
  {
    GenericType genericType = (GenericType) term_;
    genericType.setOptionalType(optionalType);
  }

  public Type2 getOptionalType()
  {
    GenericType genericType = (GenericType) term_;
    Type2 result = genericType.getOptionalType();
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
    GenericType genericType = (GenericType) term_;
    return genericType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof GenericType) {
      GenericType gType = (GenericType) obj;
      if (!getName().equals(gType.getName()) ||
          !getType().equals(gType.getType())) {
        return false;
      }

      if (getOptionalType() != null && gType.getOptionalType() != null) {
        return getOptionalType().equals(gType.getOptionalType());
      }
      else if (getOptionalType() == null && gType.getOptionalType() == null) {
        return true;
      }
      else {
        return false;
      }
    }
    return false;
  }
}
