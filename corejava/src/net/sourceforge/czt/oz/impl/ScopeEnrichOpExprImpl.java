
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

package net.sourceforge.czt.oz.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;

import net.sourceforge.czt.oz.visitor.ScopeEnrichOpExprVisitor;

/**
 * An implementation of the interface
 * {@link ScopeEnrichOpExpr}.
 *
 * @author Gnast version 0.1
 */
public class ScopeEnrichOpExprImpl
  extends OperationExprImpl   implements ScopeEnrichOpExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.oz.ast.OzFactory object factory}.
   */
  protected ScopeEnrichOpExprImpl()
  {
  }

  /**
   * Compares the specified object with this ScopeEnrichOpExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ScopeEnrichOpExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        ScopeEnrichOpExprImpl object = (ScopeEnrichOpExprImpl) obj;
        if (leftOperationExpr_ != null) {
          if (!leftOperationExpr_.equals(object.leftOperationExpr_)) {
            return false;
          }
        }
        else {
          if (object.leftOperationExpr_ != null) {
            return false;
          }
        }
        if (rightOperationExpr_ != null) {
          if (!rightOperationExpr_.equals(object.rightOperationExpr_)) {
            return false;
          }
        }
        else {
          if (object.rightOperationExpr_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this ScopeEnrichOpExprImpl.
   * The hash code of a ScopeEnrichOpExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ScopeEnrichOpExprImpl".hashCode();
    if (leftOperationExpr_ != null) {
      hashCode += constant * leftOperationExpr_.hashCode();
    }
    if (rightOperationExpr_ != null) {
      hashCode += constant * rightOperationExpr_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof ScopeEnrichOpExprVisitor) {
      ScopeEnrichOpExprVisitor visitor = (ScopeEnrichOpExprVisitor) v;
      return visitor.visitScopeEnrichOpExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    ScopeEnrichOpExpr zedObject = null;
    try {
      OperationExpr leftOperationExpr = (OperationExpr) args[0];
      OperationExpr rightOperationExpr = (OperationExpr) args[1];
      zedObject = new ScopeEnrichOpExprImpl();
      zedObject.setLeftOperationExpr(leftOperationExpr);
      zedObject.setRightOperationExpr(rightOperationExpr);
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
    Object[] erg = { getLeftOperationExpr(), getRightOperationExpr() };
    return erg;
  }

  private OperationExpr leftOperationExpr_;

  public OperationExpr getLeftOperationExpr()
  {
    return leftOperationExpr_;
  }

  public void setLeftOperationExpr(OperationExpr leftOperationExpr)
  {
    leftOperationExpr_ = leftOperationExpr;
  }

  private OperationExpr rightOperationExpr_;

  public OperationExpr getRightOperationExpr()
  {
    return rightOperationExpr_;
  }

  public void setRightOperationExpr(OperationExpr rightOperationExpr)
  {
    rightOperationExpr_ = rightOperationExpr;
  }
}
