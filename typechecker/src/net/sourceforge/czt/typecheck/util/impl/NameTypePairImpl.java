package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for NameTypePair that hides VariableType instances
 * if they have a value.
 */
public class NameTypePairImpl
  extends TermImpl
  implements NameTypePair
{
  protected NameTypePairImpl(NameTypePair nameTypePair)
  {
    super(nameTypePair);
  }

  public void setName(DeclName declName)
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    nameTypePair.setName(declName);
  }

  public DeclName getName()
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    return nameTypePair.getName();
  }

  public void setType(Type type)
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    nameTypePair.setType(type);
  }

  public Type getType()
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    Type result = nameTypePair.getType();
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
    if (obj instanceof NameTypePair) {
      NameTypePair pair = (NameTypePair) obj;
      if (!getName().equals(pair.getName()) ||
          !getType().equals(pair.getType())) {
        return false;
      }
      return true;
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "NameTypePairImpl".hashCode();
    if (getName() != null) {
      hashCode += constant * getName().hashCode();
    }
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}
