package net.sourceforge.czt.typecheck.util.typingenv;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ProdTypeImpl;

/**
 * An implementation for ProdType that hides VariableType instances
 * if they have a value.
 */
public class VProdTypeImpl
  extends ProdTypeImpl
{
  protected VProdTypeImpl()
  {
    super();
  }

  public ListTerm getType()
  {
    ListTerm result = super.getType();

    for (int i = 0; i < result.size(); i++) {
      Type2 type = (Type2) result.get(i);
      if (type instanceof VariableType) {
        VariableType vType = (VariableType) type;

        if (vType.getValue() != null) {
          result.set(i, vType.getValue());
        }
      }
    }
    return result;
  }
}
