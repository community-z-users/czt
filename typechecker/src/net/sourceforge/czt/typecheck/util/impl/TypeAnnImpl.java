package net.sourceforge.czt.typecheck.util.impl;

import java.util.List;

import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for TypeAnn that hides VariableType instances
 * if they have a value.
 */
public class TypeAnnImpl
  extends TermImpl
  implements TypeAnn
{
  protected TypeAnnImpl(TypeAnn typeAnn)
  {
    super(typeAnn);
  }

  public void setType(Type type)
  {
    TypeAnn typeAnn = (TypeAnn) term_;
    typeAnn.setType(type);
  }

  public Type getType()
  {
    TypeAnn typeAnn = (TypeAnn) term_;
    Type result = typeAnn.getType();
    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;
      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof TypeAnn) {
      TypeAnn typeAnn = (TypeAnn) obj;
      return getType().equals(typeAnn.getType());
    }
    return false;
  }
}
