package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Type;

/**
 * <code>UnknownType</code> is used when gathering type information
 * in the case when a type is used before it is declared. This is
 * legal in Object-Z
 */
public interface UnknownType extends Type
{
  /**
   * Get the undefined name associated with this type
   */
  public DeclName getName();

  /**
   * Set the undefined name associated with this type
   */
  public void setName(DeclName declName);
}
