
/*
THIS FILE WAS GENERATED BY GNAST.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

************************************************************

Copyright 2003 Mark Utting
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

package net.sourceforge.czt.z.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z.visitor.BindSelExprVisitor;

/**
 * An implementation of the interface
 * {@link BindSelExpr}.
 *
 * @author Gnast version 0.1
 */
public class BindSelExprImpl
  extends Expr1Impl   implements BindSelExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.z.ast.ZFactory object factory}.
   */
  protected BindSelExprImpl()
  {
  }

  /**
   * Compares the specified object with this BindSelExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) BindSelExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        BindSelExprImpl object = (BindSelExprImpl) obj;
        if (name_ != null) {
          if (!name_.equals(object.name_)) {
            return false;
          }
        }
        else {
          if (object.name_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this BindSelExprImpl.
   * The hash code of a BindSelExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "BindSelExprImpl".hashCode();
    if (name_ != null) {
      hashCode += constant * name_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof BindSelExprVisitor) {
      BindSelExprVisitor visitor = (BindSelExprVisitor) v;
      return visitor.visitBindSelExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    BindSelExpr zedObject = null;
    try {
      Expr expr = (Expr) args[0];
      RefName name = (RefName) args[1];
      zedObject = new BindSelExprImpl();
      zedObject.setExpr(expr);
      zedObject.setName(name);
    }
    catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    }
    catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getExpr(), getName() };
    return erg;
  }

  private RefName name_;

  public RefName getName()
  {
    return name_;
  }

  public void setName(RefName name)
  {
    name_ = name;
  }
}
