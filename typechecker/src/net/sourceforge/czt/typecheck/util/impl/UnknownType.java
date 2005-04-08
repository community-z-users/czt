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
package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.impl.Type2Impl;

/**
 * <code>UnknownTypeImpl</code> is an implementation of
 * <code>UnknownType</code>.
 */
public class UnknownType
  extends Type2Impl
{
  /** The undefined name associated with this type. */
  protected DeclName declName_;

  protected UnknownType()
  {
    declName_ = null;
  }

  protected UnknownType(DeclName declName)
  {
    declName_ = declName;
  }

  /**
   * Get the undefined name associated with this type.
   */
  public DeclName getName()
  {
    return declName_;
  }

  /**
   * Set the undefined name associated with this type.
   */
  public void setName(DeclName declName)
  {
    declName_ = declName;
  }

  public boolean equals(Object obj)
  {
    boolean result = false;

    if (obj instanceof UnknownType) {
      UnknownType unknownType = (UnknownType) obj;
      if (declName_ == null && unknownType.getName() == null) {
        result = true;
      }
      else if (declName_ != null && declName_.equals(unknownType.getName())) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "UnknownType".hashCode();
    if (declName_ != null) {
      hashCode += constant * declName_.hashCode();
    }
    return hashCode;

  }

  public Object [] getChildren()
  {
    Object [] children = { getName() };
    return children;
  }

  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof UnknownTypeVisitor) {
      UnknownTypeVisitor visitor = (UnknownTypeVisitor) v;
      return visitor.visitUnknownType(this);
    }
    return super.accept(v);
  }

  public Term create(java.lang.Object[] args)
  {
    UnknownType zedObject = null;
    try {
      zedObject = new UnknownType();
      DeclName declName = (DeclName) args[0];
      zedObject.setName(declName);
    }
    catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    }
    catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public String toString()
  {
    String result = "unknown";

    if (declName_ != null) {
      result += "(" + declName_.toString() + ")";
    }
    return result;
  }
}
