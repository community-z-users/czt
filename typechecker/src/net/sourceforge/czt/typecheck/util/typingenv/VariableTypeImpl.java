package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.ArrayList;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.impl.Type2Impl;

/**
 * An implementation for VariableType.
 */
public class VariableTypeImpl
  extends Type2Impl
  implements VariableType
{
  /**
   * The Greek alpha character as a string. Prefix with an underscore
   * to avoid clashes with user-defined variables.
   */
  protected static final String ALPHA = "_" + Character.toString('\u03B1');

  /** The number stroke of the next alpha variable. */
  protected static int serial_ = 0;

  /** The name of this variable. */
  protected DeclName declName_ = null;

  /** The types that depend on this variable */
  protected List dependents_ = new ArrayList();

  /** A ZFactory. */
  protected ZFactory factory_ = null;

  protected VariableTypeImpl()
  {
    super();
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    List strokes = new ArrayList();
    strokes.add(factory_.createNumStroke(new Integer(serial_++)));
    declName_ = factory_.createDeclName(ALPHA, strokes, null);
  }

  protected VariableTypeImpl(DeclName declName)
  {
    super();
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    declName_ = declName;
  }

  /**
   * Get the variable name associated with this type.
   */
  public DeclName getName()
  {
    return declName_;
  }

  /**
   * Set the variable name associated with this type.
   */
  public void setName(DeclName declName)
  {
    declName_ = declName;
  }

  /**
   * Gets the types that depend on this type
   */
  public List getDependent()
  {
    return dependents_;
  }

  public Object[] getChildren()
  {
    Object[] result = { };
    return result;
  }

  public static VariableType create()
  {
    return new VariableTypeImpl();
  }

  public static VariableType create(DeclName declName)
  {
    return new VariableTypeImpl(declName);
  }

  public Term create(Object[] args)
  {
    return new VariableTypeImpl();
  }

  public String toString()
  {
    String result = new String();

    if (declName_.getWord().indexOf(ALPHA) >= 0) {
      result += declName_.toString();
    }
    else {
      result += "VTYPE(" + declName_.toString() + ")";
    }

    return result;
  }

  public boolean equals(Object o)
  {
    boolean result = false;

    if (o instanceof VariableType) {
      VariableType variableType = (VariableType) o;
      if (declName_.equals(variableType.getName())) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "VariableTypeImpl".hashCode();
    if (declName_ != null) {
      hashCode += constant * declName_.hashCode();
    }
    return hashCode;
  }

  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof VariableTypeVisitor) {
      VariableTypeVisitor visitor = (VariableTypeVisitor) v;
      return visitor.visitVariableType(this);
    }
    return super.accept(v);
  }
}
