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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.impl.Type2Impl;

/**
 * <code>UnknownTypeImpl</code> is an implementation of
 * <code>UnknownType</code>.
 */
public class UnknownType
  extends Type2Impl
{
  /** The undefined reference associated with this type. */
  protected RefExpr refExpr_;

  /** True iff refExpr_ is the superset of this type. */
  protected boolean isMem_;

  protected UnknownType()
  {
    refExpr_ = null;
    isMem_ = false;
  }

  protected UnknownType(RefExpr refExpr)
  {
    this();
    refExpr_ = refExpr;
  }

  /**
   * Get the undefined reference associated with this type.
   */
  public RefExpr getRefExpr()
  {
    return refExpr_;
  }

  /**
   * Set the undefined reference associated with this type.
   */
  public void setRefExpr(RefExpr refExpr)
  {
    refExpr_ = refExpr;
  }

  public void setIsMem(boolean isMem)
  {
    isMem_ = isMem;
  }

  public boolean getIsMem()
  {
    return isMem_;
  }

  public boolean equals(Object obj)
  {
    boolean result = false;

    if (obj instanceof UnknownType) {
      UnknownType unknownType = (UnknownType) obj;
      if (refExpr_ == null && unknownType.getRefExpr() == null) {
        result = true;
      }
      else if (refExpr_ != null && refExpr_.equals(unknownType.getRefExpr())) {
        result = true;
      }

      if (result && isMem_ == unknownType.getIsMem()) {
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
    if (refExpr_ != null) {
      hashCode += constant * refExpr_.hashCode();
    }
    return hashCode;

  }

  public Object [] getChildren()
  {
    Object [] children = { getRefExpr(), new Boolean(getIsMem()) };
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
      RefExpr refExpr = (RefExpr) args[0];
      Boolean isMem = (Boolean) args[1];
      zedObject.setRefExpr(refExpr);
      zedObject.setIsMem(isMem);
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

    if (refExpr_ != null) {
      result += "(";
      if (getIsMem()) {
	result += "member(";
      }
      result += refExpr_.getRefName() + ")";
      if (getIsMem()) {
	result += ")";
      }      
    }
    return result;
  }
}
