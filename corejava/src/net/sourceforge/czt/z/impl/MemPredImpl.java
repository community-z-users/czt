
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

package net.sourceforge.czt.z.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z.visitor.MemPredVisitor;

/**
 * An implementation of the interface
 * {@link MemPred}.
 *
 * @author Gnast version 0.1
 */
public class MemPredImpl
  extends PredImpl   implements MemPred
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.z.ast.ZFactory object factory}.
   */
  protected MemPredImpl()
  {
  }

  /**
   * Compares the specified object with this MemPredImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) MemPredImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        MemPredImpl object = (MemPredImpl) obj;
        if (leftExpr_ != null) {
          if (!leftExpr_.equals(object.leftExpr_)) {
            return false;
          }
        }
        else {
          if (object.leftExpr_ != null) {
            return false;
          }
        }
        if (rightExpr_ != null) {
          if (!rightExpr_.equals(object.rightExpr_)) {
            return false;
          }
        }
        else {
          if (object.rightExpr_ != null) {
            return false;
          }
        }
        if (mixfix_ != null) {
          if (!mixfix_.equals(object.mixfix_)) {
            return false;
          }
        }
        else {
          if (object.mixfix_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this MemPredImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "MemPredImpl".hashCode();
    if (leftExpr_ != null) {
      hashCode += constant * leftExpr_.hashCode();
    }
    if (rightExpr_ != null) {
      hashCode += constant * rightExpr_.hashCode();
    }
    if (mixfix_ != null) {
      hashCode += constant * mixfix_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof MemPredVisitor) {
      MemPredVisitor visitor = (MemPredVisitor) v;
      return visitor.visitMemPred(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    MemPred zedObject = null;
    try {
      Expr leftExpr = (Expr) args[0];
      Expr rightExpr = (Expr) args[1];
      Boolean mixfix = (Boolean) args[2];
      zedObject = new MemPredImpl();
      zedObject.setLeftExpr(leftExpr);
      zedObject.setRightExpr(rightExpr);
      zedObject.setMixfix(mixfix);
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
    Object[] erg = { getLeftExpr(), getRightExpr(), getMixfix() };
    return erg;
  }

  private Expr leftExpr_;

  public Expr getLeftExpr()
  {
    return leftExpr_;
  }

  public void setLeftExpr(Expr leftExpr)
  {
    leftExpr_ = leftExpr;
  }

  private Expr rightExpr_;

  public Expr getRightExpr()
  {
    return rightExpr_;
  }

  public void setRightExpr(Expr rightExpr)
  {
    rightExpr_ = rightExpr;
  }

  private Boolean mixfix_;

  public Boolean getMixfix()
  {
    return mixfix_;
  }

  public void setMixfix(Boolean mixfix)
  {
    mixfix_ = mixfix;
  }

  public boolean isEquality()
  {
    final boolean mixfix = getMixfix().booleanValue();
    final Expr firstExpr = getLeftExpr();
    final Expr secondExpr = getRightExpr();
    if (mixfix && secondExpr instanceof SetExpr) {
      SetExpr setExpr = (SetExpr) secondExpr;
      if (setExpr.getExpr().size() == 1) {
        return true;
      }
    }
    return false;
  }
}
