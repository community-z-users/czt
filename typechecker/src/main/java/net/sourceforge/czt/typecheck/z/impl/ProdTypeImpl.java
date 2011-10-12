/*
  Copyright (C) 2004 Tim Miller
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.typecheck.z.impl;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

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

  public ListTerm<Type2> getType()
  {
    ProdType prodType = (ProdType) term_;
    ListTerm<Type2> result = prodType.getType();
    for (int i = 0; i < result.size(); i++) {
      Type2 type = (Type2) result.get(i);
      if (type instanceof VariableType) {
        VariableType vType = (VariableType) type;
        if (vType.getValue() != vType) {
          result.set(i, vType.getValue());
        }
      }
    }
    return result;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getType() };
    return erg;
  }

  public ProdTypeImpl create(Object [] args)
  {
    ProdType prodType = (ProdType) term_.create(args);
    ProdTypeImpl result = new ProdTypeImpl(prodType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof ProdTypeVisitor) {
      ProdTypeVisitor<R> visitor = (ProdTypeVisitor<R>) v;
      return visitor.visitProdType(this);
    }
    return super.accept(v);
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

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ProdTypeImpl".hashCode();
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}
