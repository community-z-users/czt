package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for Term that hides VariableType instances
 * if they have a value.
 */
public class TermAImpl
  extends TermImpl
  implements TermA
{
  protected TermAImpl(TermA termA)
  {
    super(termA);
  }

  public ListTerm getAnns()
  {
    return ((TermA) term_).getAnns();
  }

  public Object getAnn(Class aClass)
  {
    return ((TermA) term_).getAnn(aClass);
  }
}
