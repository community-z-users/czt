package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for Type2 that hides VariableType instances
 * if they have a value.
 */
public class Type2Impl
  extends TypeImpl
  implements Type2
{
  protected Type2Impl(Type2 type)
  {
    super(type);
  }
}
