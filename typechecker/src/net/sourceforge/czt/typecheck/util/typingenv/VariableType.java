package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.DeclName;

public interface VariableType extends Type
{
  /**
   * Get the variable name associated with this type
   */
  public DeclName getName();

  /**
   * Set the variable name associated with this type
   */
  public void setName(DeclName declName);
}
