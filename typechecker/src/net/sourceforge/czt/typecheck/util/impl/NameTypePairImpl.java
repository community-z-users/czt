package net.sourceforge.czt.typecheck.util.impl;

import java.util.List;

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
}
