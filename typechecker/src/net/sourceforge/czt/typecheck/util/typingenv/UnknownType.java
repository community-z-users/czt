package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Type2;

/**
 * <code>UnknownType</code> is used when gathering type information
 * in the case when a type is used before it is declared. This is
 * legal in Object-Z.
 */
public interface UnknownType extends Type2
{
  /**
   * Get the undefined name associated with this type.
   */
  DeclName getName();

  /**
   * Set the undefined name associated with this type.
   */
  void setName(DeclName declName);

  /**
   * Return true iff we should use the base type of the declname
   * as the type for this. Return false if we use the type itself
   * i.e. a constant declaration.
   */
  boolean useBaseType();

  /**
   * Determines whether this unknown type is the type of the variable,
   * or the subtype.
   */
  void setUseBaseType(boolean useBaseType);
}
