package net.sourceforge.czt.typecheck.util.typingenv;


import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;

public final class EmptyType
  implements Type
{
  public ListTerm getAnns()
  {
    return new ListTermImpl(Object.class);
  }

  public Object accept(Visitor visitor)
  {
    return this;
  }

  public Term create(Object[] args)
  {
    return null;
  }

  public Object[] getChildren()
  {
    return null;
  }
}
