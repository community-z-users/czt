package net.sourceforge.czt.typecheck.util.impl;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.impl.Type2Impl;

/**
 * A VariableType.
 */
public class VariableType
  extends Type2Impl
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

  /** The value of this variable. */
  protected Type2 value_ = null;

  protected VariableType()
  {
    super();
    Factory factory = new Factory();
    List strokes = new java.util.ArrayList();
    strokes.add(factory.createNumStroke(new Integer(serial_++)));
    declName_ = factory.createDeclName(ALPHA, strokes, null);
  }

  protected VariableType(DeclName declName)
  {
    super();
    declName_ = declName;
  }

  /**
   * @return The value of this variable, or itself if no value as been
   * assigned.
   */
  public Type2 getValue()
  {
    if (value_ == null) {
      return this;
    }
    else {
      if (value_ instanceof VariableType) {
        VariableType vType = (VariableType) value_;
        return vType.getValue();
      }
      return value_;
    }
  }

  /**
   * Sets the value of this variable.
   * @param type - the value of this variable.
   */
  public void setValue(Type2 value)
  {
    if (value_ instanceof VariableType) {
      VariableType vType = (VariableType) value_;
      vType.setValue(value);
    }
    else {
      value_ = value;
    }
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

  public Object[] getChildren()
  {
    Object[] result = { getName(), getValue() };
    return result;
  }

  public static VariableType create()
  {
    return new VariableType();
  }

  public static VariableType create(DeclName declName)
  {
    return new VariableType(declName);
  }

  public Term create(Object[] args)
  {
    return new VariableType();
  }

  public String toString()
  {
    String result = new String();

    if (value_ != null) {
      result += value_.toString();
    }
    else if (declName_.getWord().indexOf(ALPHA) >= 0) {
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
    hashCode += "VariableType".hashCode();
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
