package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.util.OperatorName;
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
  //the undefined name associated with this type.
  private DeclName declName_;

  private UnknownTypeImpl()
  {
    declName_ = null;
  }

  private UnknownTypeImpl(DeclName declName)
  {
    declName_ = declName;
  }

  /**
   * Get the undefined name associated with this type.
   */
  public DeclName getName()
  {
    return declName_;
  }

  /**
   * Set the undefined name associated with this type.
   */
  public void setName(DeclName declName)
  {
    declName_ = declName;
  }

  static public UnknownType create()
  {
    return new UnknownTypeImpl();
  }

  static public UnknownType create(DeclName declName)
  {
    return new UnknownTypeImpl(declName);
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
    String result = "unknown";

    if (declName_ != null) {
      result += "(" + declName_.toString() + ")";
    }
    return result;
  }
}
