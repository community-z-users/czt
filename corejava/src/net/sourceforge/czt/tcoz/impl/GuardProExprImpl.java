
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstClass.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004 Mark Utting
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
******************************************************************************/

package net.sourceforge.czt.tcoz.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.impl.*;
import net.sourceforge.czt.tcoz.ast.*;
import net.sourceforge.czt.tcoz.visitor.*;

import net.sourceforge.czt.tcoz.visitor.GuardProExprVisitor;

/**
 * An implementation of the interface
 * {@link GuardProExpr}.
 *
 * @author Gnast version 0.1
 */
public class GuardProExprImpl
  extends OpExprImpl   implements GuardProExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.tcoz.ast.TcozFactory object factory}.
   */
  protected GuardProExprImpl()
  {
  }

  /**
   * Compares the specified object with this GuardProExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) GuardProExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        GuardProExprImpl object = (GuardProExprImpl) obj;
        if (guard_ != null) {
          if (!guard_.equals(object.guard_)) {
            return false;
          }
        }
        else {
          if (object.guard_ != null) {
            return false;
          }
        }
        if (opExpr_ != null) {
          if (!opExpr_.equals(object.opExpr_)) {
            return false;
          }
        }
        else {
          if (object.opExpr_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this GuardProExprImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "GuardProExprImpl".hashCode();
    if (guard_ != null) {
      hashCode += constant * guard_.hashCode();
    }
    if (opExpr_ != null) {
      hashCode += constant * opExpr_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof GuardProExprVisitor) {
      GuardProExprVisitor visitor = (GuardProExprVisitor) v;
      return visitor.visitGuardProExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    GuardProExpr zedObject = null;
    try {
      net.sourceforge.czt.z.ast.SchText guard = (net.sourceforge.czt.z.ast.SchText) args[0];
      net.sourceforge.czt.oz.ast.OpExpr opExpr = (net.sourceforge.czt.oz.ast.OpExpr) args[1];
      zedObject = new GuardProExprImpl();
      zedObject.setGuard(guard);
      zedObject.setOpExpr(opExpr);
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
    Object[] erg = { getGuard(), getOpExpr() };
    return erg;
  }

  private net.sourceforge.czt.z.ast.SchText guard_;

  public net.sourceforge.czt.z.ast.SchText getGuard()
  {
    return guard_;
  }

  public void setGuard(net.sourceforge.czt.z.ast.SchText guard)
  {
    guard_ = guard;
  }

  private net.sourceforge.czt.oz.ast.OpExpr opExpr_;

  public net.sourceforge.czt.oz.ast.OpExpr getOpExpr()
  {
    return opExpr_;
  }

  public void setOpExpr(net.sourceforge.czt.oz.ast.OpExpr opExpr)
  {
    opExpr_ = opExpr;
  }
}
