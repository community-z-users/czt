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
 * An implementation for SchemaType that hides VariableSignature
 * instances if they have a value.
 */
public class SchemaTypeImpl
  extends Type2Impl
  implements SchemaType
{
  protected SchemaTypeImpl(SchemaType schemaType)
  {
    super(schemaType);
  }

  public void setSignature(Signature signature)
  {
    SchemaType schemaType = (SchemaType) term_;
    schemaType.setSignature(signature);
  }

  public Signature getSignature()
  {
    SchemaType schemaType = (SchemaType) term_;
    Signature result = schemaType.getSignature();
    if (result instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) result;
      if (vSig.getValue() != vSig) {
        result = vSig.getValue();
      }
    }
    return result;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getSignature() };
    return erg;
  }

  public SchemaTypeImpl create(Object [] args)
  {
    SchemaType schemaType = (SchemaType) term_.create(args);
    SchemaTypeImpl result = new SchemaTypeImpl(schemaType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof SchemaTypeVisitor) {
      SchemaTypeVisitor<R> visitor = (SchemaTypeVisitor<R>) v;
      return visitor.visitSchemaType(this);
    }
    return super.accept(v);
  }

  public String toString()
  {
    SchemaType schemaType = (SchemaType) term_;
    return schemaType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) obj;
      return getSignature().equals(schemaType.getSignature());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "SchemaTypeImpl".hashCode();
    if (getSignature() != null) {
      hashCode += constant * getSignature().hashCode();
    }
    return hashCode;
  }
}
