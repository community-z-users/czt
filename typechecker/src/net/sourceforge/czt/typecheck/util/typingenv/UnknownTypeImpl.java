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

  //true iff we should use the subtype of the declname
  //as the type for this. false if we use the type itself
  //i.e. a constant declaration
  private boolean useSubType_;

  private UnknownTypeImpl()
  {
    declName_ = null;
    useSubType_ = true;
  }

  private UnknownTypeImpl(DeclName declName, boolean useSubType)
  {
    declName_ = declName;
    useSubType_ = useSubType;
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

  public boolean useSubType()
  {
    return useSubType_;
  }

  public void setUseSubType(boolean useSubType)
  {
    useSubType_ = useSubType;
  }

  static public UnknownType create()
  {
    return new UnknownTypeImpl();
  }

  static public UnknownType create(DeclName declName, boolean useSubType)
  {
    return new UnknownTypeImpl(declName, useSubType);
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
