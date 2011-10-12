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
 * An implementation for GenericType that hides VariableType instances
 * if they have a value.
 */
public class GenericTypeImpl
  extends TypeImpl
  implements GenericType
{
  protected GenericTypeImpl(GenericType genericType)
  {
    super(genericType);
  }

  public NameList getNameList()
  {
    GenericType genericType = (GenericType) term_;
    return genericType.getNameList();
  }

  public ZNameList getZNameList()
  {
    GenericType genericType = (GenericType) term_;
    return genericType.getZNameList();
  }

  public void setNameList(NameList list)
  {
    GenericType genericType = (GenericType) term_;
    genericType.setNameList(list);
  }

  public ListTerm<net.sourceforge.czt.z.ast.Type2> getType()
  {
    GenericType genericType = (GenericType) term_;
    return genericType.getType();
  }

  public String toString()
  {
    GenericType genericType = (GenericType) term_;
    return genericType.toString();
  }

  public Object[] getChildren()
  {
    Object[] erg = { getNameList(), getType() };
    return erg;
  }

  public GenericTypeImpl create(Object [] args)
  {
    GenericType genericType = (GenericType) term_.create(args);
    GenericTypeImpl result = new GenericTypeImpl(genericType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof GenericTypeVisitor) {
      GenericTypeVisitor<R> visitor = (GenericTypeVisitor<R>) v;
      return visitor.visitGenericType(this);
    }
    return super.accept(v);
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof GenericType) {
      GenericType gType = (GenericType) obj;
      if (!getNameList().equals(gType.getNameList()) ||
          !getType().equals(gType.getType())) {
        return false;
      }
      if (getType().size() == gType.getType().size()) {
	if (! getType().get(0).equals(gType.getType().get(0))) return false;
	if (getType().size() > 1) {
	  return getType().get(1).equals(gType.getType().get(1));
	}
	else {
	  return true;
	}
      }
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "GenericTypeImpl".hashCode();
    if (getNameList() != null) {
      hashCode += constant * getNameList().hashCode();
    }
    for (Type2 type : getType()) {
      hashCode += constant * type.hashCode();
    }
    return hashCode;
  }
}
