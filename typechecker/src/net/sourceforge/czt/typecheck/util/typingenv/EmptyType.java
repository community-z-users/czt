package net.sourceforge.czt.typecheck.util.typingenv;


import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.z.impl.TypeImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;

public final class EmptyType
  extends TypeImpl
{
  public Object[] getChildren()
  {
    Object[] result = {  };
    return result;
  }

  public Term create(Object[] args)
  {
    return new EmptyType();
  }
}
