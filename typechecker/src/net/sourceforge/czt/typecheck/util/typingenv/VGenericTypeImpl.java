package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.GenericTypeImpl;

/**
 * An implementation for GenericType that hides VariableType instances
 * if they have a value.
 */
public class VGenericTypeImpl
  extends GenericTypeImpl
{
  protected VGenericTypeImpl()
  {
    super();
  }

  public Type2 getOptionalType()
  {
    Type2 result = super.getOptionalType();

    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;

      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }
}
