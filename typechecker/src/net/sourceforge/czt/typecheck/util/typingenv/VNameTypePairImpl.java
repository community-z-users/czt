package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.NameTypePairImpl;

/**
 * An implementation for NameTypePair that hides VariableType instances
 * if they have a value.
 */
public class VNameTypePairImpl
  extends NameTypePairImpl
{
  protected VNameTypePairImpl()
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
