package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.ArrayList;

import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.impl.SignatureImpl;

/**
 * An implementation for Signature that represents a signature variable.
 */
public class VariableSignature
  extends SignatureImpl
  implements Signature
{
  /**
   * The Greek beta character as a string. Prefix with an
   * underscore to avoid clashes with user-defined variables.
   */
  protected static final String BETA = "_" + Character.toString('\u03B2');

  /** The number stroke of the next beta variable. */
  protected static int serial_ = 0;

  /** The name of this variable. */
  protected DeclName declName_ = null;

  /** The types that depend on this variable. */
  protected List dependents_ = new ArrayList();

  /** A ZFactory. */
  protected ZFactory factory_ = null;

  protected VariableSignature()
  {
    super();
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    List strokes = new ArrayList();
    strokes.add(factory_.createNumStroke(new Integer(serial_++)));
    declName_ = factory_.createDeclName(BETA, strokes, null);
  }

  protected VariableSignature(DeclName declName)
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
   * Gets the types that depend on this type.
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

  public static VariableSignature create()
  {
    return new VariableSignature();
  }

  public static VariableSignature create(DeclName declName)
  {
    return new VariableSignature(declName);
  }

  public String toString()
  {
    return declName_.toString();
  }

  public boolean equals(Object o)
  {
    boolean result = false;

    if (o instanceof VariableSignature) {
      VariableSignature variableSignature = (VariableSignature) o;
      if (declName_.equals(variableSignature.getName())) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "VariableSignature".hashCode();
    if (declName_ != null) {
      hashCode += constant * declName_.hashCode();
    }
    return hashCode;
  }
}
