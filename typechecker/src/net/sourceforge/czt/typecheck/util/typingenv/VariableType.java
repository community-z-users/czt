package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.z.impl.TypeImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;

public class VariableType
  extends TypeImpl
{
  private static int serial_ = 0;
  private String name_;

  public VariableType()
  {
    super();
    name_ = new String("_alpha_" + Integer.toString(serial_++));
  }

  /**
   * Create a variable type from a generic type.
   */
  public VariableType(String n)
  {
    super();
    name_ = n;
  }

  public Object[] getChildren()
  {
    Object[] result = {  };
    return result;
  }

  public Term create(Object[] args)
  {
    return null;
  }
}
