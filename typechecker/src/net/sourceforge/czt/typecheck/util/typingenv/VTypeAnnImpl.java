package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.TypeAnnImpl;

/**
 * An implementation for TypeAnn that hides VariableType instances
 * if they have a value.
 */
public class VTypeAnnImpl
  extends TypeAnnImpl
{
  protected VTypeAnnImpl()
  {
    super();
  }

  public Type getType()
  {
    Type result = super.getType();

    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;

      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }
}
