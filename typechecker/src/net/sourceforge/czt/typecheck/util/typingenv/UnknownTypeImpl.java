package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.impl.Type2Impl;

/**
 * <code>UnknownTypeImpl</code> is an implementation of
 * <code>UnknownType</code>.
 */
public final class UnknownTypeImpl
  extends Type2Impl
  implements UnknownType
{
  /** The undefined name associated with this type. */
  protected DeclName declName_;

  /**
   * True iff we should use the subtype of the declname as the type
   * for this. False if we use the type itself i.e. a constant
   * declaration.
   */
  protected boolean useBaseType_;

  private UnknownTypeImpl()
  {
    declName_ = null;
    useBaseType_ = true;
  }

  private UnknownTypeImpl(DeclName declName, boolean useBaseType)
  {
    declName_ = declName;
    useBaseType_ = useBaseType;
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

  public boolean useBaseType()
  {
    return useBaseType_;
  }

  public void setUseBaseType(boolean useBaseType)
  {
    useBaseType_ = useBaseType;
  }

  public static UnknownType create()
  {
    return new UnknownTypeImpl();
  }

  public static UnknownType create(DeclName declName, boolean useBaseType)
  {
    return new UnknownTypeImpl(declName, useBaseType);
  }

  public boolean equals(Object obj)
  {
    boolean result = false;

    if (obj instanceof UnknownType) {
      UnknownType unknownType = (UnknownType) obj;
      if (declName_ != null && declName_.equals(unknownType.getName())) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "UnknownTypeImpl".hashCode();
    if (declName_ != null) {
      hashCode += constant * declName_.hashCode();
    }
    return hashCode;

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
