package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.DeclName;

/**
 * A variable type.
 */
public interface VariableType extends Type2
{
  /**
   * @return The value of this variable, or itself if no value as been
   * assigned.
   */
  Type2 getValue();

  /**
   * Sets the value of this variable.
   * @param type - the value of this variable
   */
  void setValue(Type2 type);

  /**
   * @return Get the variable name associated with this type.
   */
  DeclName getName();

  /**
   * Set the variable name associated with this type.
   */
  void setName(DeclName declName);
}
