package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for Term that hides VariableType instances
 * if they have a value.
 */
public class TermImpl
  implements Term
{
  /** The Term that this type wraps. */
  protected Term term_;

  protected TermImpl(Term term)
  {
    term_ = term;
  }

  public boolean equals(Object obj)
  {
    return term_.equals(obj);
  }

  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    return term_.accept(v);
  }

  public Object [] getChildren()
  {
    return term_.getChildren();
  }

  public net.sourceforge.czt.base.ast.Term create(Object [] args)
  {
    return term_.create(args);
  }

  public int hashCode()
  {
    return term_.hashCode();
  }
}
