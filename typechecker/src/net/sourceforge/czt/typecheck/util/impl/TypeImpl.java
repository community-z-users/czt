package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for Type that hides VariableType instances
 * if they have a value.
 */
public class TypeImpl
  extends TermAImpl
  implements Type
{
  protected TypeImpl(Type type)
  {
    super(type);
  }
}
