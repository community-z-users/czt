package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.impl.Type2Impl;

/**
 * <code>UnknownTypeImpl</code> is an implementation of
 * <code>UnknownType</code>.
 */
public class UnknownType
  extends Type2Impl
{
  /** The undefined name associated with this type. */
  protected DeclName declName_;

  protected UnknownType()
  {
    declName_ = null;
  }

  protected UnknownType(DeclName declName)
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
    hashCode += "UnknownType".hashCode();
    if (declName_ != null) {
      hashCode += constant * declName_.hashCode();
    }
    return hashCode;

  }

  public Object [] getChildren()
  {
    Object [] children = { getName() };
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
    UnknownType zedObject = null;
    try {
      zedObject = new UnknownType();
      if (args.length == 1) {
        DeclName declName = (DeclName) args[0];
        zedObject.setName(declName);
      }
    }
    catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    }
    catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
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
