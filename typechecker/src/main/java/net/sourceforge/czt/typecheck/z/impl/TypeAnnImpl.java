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

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for TypeAnn that hides VariableType instances
 * if they have a value.
 */
public class TypeAnnImpl
  extends AnnImpl
  implements TypeAnn
{
  protected TypeAnnImpl(TypeAnn typeAnn)
  {
    super(typeAnn);
  }

  public void setType(Type type)
  {
    TypeAnn typeAnn = (TypeAnn) term_;
    typeAnn.setType(type);
  }

  public Type getType()
  {
    TypeAnn typeAnn = (TypeAnn) term_;
    Type result = typeAnn.getType();
    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;
      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getType() };
    return erg;
  }

  public TypeAnnImpl create(Object [] args)
  {
    TypeAnn typeAnn = (TypeAnn) term_.create(args);
    TypeAnnImpl result = new TypeAnnImpl(typeAnn);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof TypeAnnVisitor) {
      TypeAnnVisitor<R> visitor = (TypeAnnVisitor<R>) v;
      return visitor.visitTypeAnn(this);
    }
    return super.accept(v);
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof TypeAnn) {
      TypeAnn typeAnn = (TypeAnn) obj;
      return getType().equals(typeAnn.getType());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "TypeAnnImpl".hashCode();
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}
