package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for ProdType that hides VariableType instances
 * if they have a value.
 */
public class ProdTypeImpl
  extends Type2Impl
  implements ProdType
{
  protected ProdTypeImpl(ProdType prodType)
  {
    super(prodType);
  }

  public ListTerm getType()
  {
    ProdType prodType = (ProdType) term_;
    ListTerm result = prodType.getType();
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

  public String toString()
  {
    ProdType prodType = (ProdType) term_;
    return prodType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof ProdType) {
      ProdType prodType = (ProdType) obj;
      if (getType().size() == prodType.getType().size()) {
        for (int i = 0; i < getType().size(); i++) {
          Type2 typeA = (Type2) getType().get(i);
          Type2 typeB = (Type2) prodType.getType().get(i);
          if (!typeA.equals(typeB)) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }
}
