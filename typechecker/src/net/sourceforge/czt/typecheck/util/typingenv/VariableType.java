package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.DeclName;

/**
 * A variable type.
 */
public interface VariableType extends Type2
{
  /**
   * Get the variable name associated with this type.
   */
  DeclName getName();

  /**
   * Set the variable name associated with this type.
   */
  void setName(DeclName declName);
}
