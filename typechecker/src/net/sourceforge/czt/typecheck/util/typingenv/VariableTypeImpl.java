package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.ArrayList;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.impl.TypeImpl;

/**
 * An implementation for VariableType.
 */
public class VariableTypeImpl
  extends TypeImpl
  implements VariableType
{
  /** The Greek alpha character as a string. */
  protected static final String ALPHA = Character.toString('\u03B1');

  /** The number stroke of the next alpha variable. */
  protected static int serial_ = 0;

  /** The name of this variable. */
  protected DeclName declName_ = null;

  /** A ZFactory. */
  protected ZFactory factory_ = null;

  private VariableTypeImpl()
  {
    super();
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    List strokes = new ArrayList();
    strokes.add(factory_.createNumStroke(new Integer(serial_++)));
    declName_ = factory_.createDeclName(ALPHA, strokes, null);
  }

  private VariableTypeImpl(DeclName declName)
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

  public Object[] getChildren()
  {
    Object[] result = { };
    return result;
  }

  public Term create()
  {
    return new VariableTypeImpl();
  }

  public Term create(DeclName declName)
  {
    return new VariableTypeImpl(declName);
  }

  public Term create(Object[] args)
  {
    return new VariableTypeImpl();
  }

  public String toString()
  {
    return declName_.toString();
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
}
