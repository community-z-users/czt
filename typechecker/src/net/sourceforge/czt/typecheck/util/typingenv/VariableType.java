package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;

public class VariableType implements Type
{
  private static int serial_ = 0;
  private String name_;

  public VariableType()
  {
    name_ = new String("_alpha_" + Integer.toString(serial_++));
  }

  /**
   * Create a variable type from a generic type.
   */
  public VariableType(String n)
  {
    name_ = n;
  }

  public List getAnns()
  {
    return new Vector();
  }

  public Object accept(Visitor visitor)
  {
    return this;
  }

  public Term create(Object[] args)
  {
    return null;
  }

  public Object[] getChildren()
  {
    return null;
  }
}
