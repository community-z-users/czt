package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.impl.TypeImpl;

/**
 * <code>UnknownTypeImpl</code> is an implementation of
 * <code>UnknownType</code>
 */
public class UnknownTypeImpl 
  extends TypeImpl 
  implements UnknownType
{
  private UnknownTypeImpl()
  {
  }

  static public UnknownType create()
  {
    return new UnknownTypeImpl();
  }

  public boolean equals(Object obj)
  {
    return false;
  }

  public Object [] getChildren()
  {
    Object [] children = {};
    return children;
  }

  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof UnknownTypeVisitor) {
      UnknownTypeVisitor visitor = (UnknownTypeVisitor) v;
      return visitor.visitUnknownType(this);
    }
    return super.accept(v);
  }

  public Term create(java.lang.Object[] args)
  {
    return create();
  }

  public String toString()
  {
    return "unknown";
  }
}
