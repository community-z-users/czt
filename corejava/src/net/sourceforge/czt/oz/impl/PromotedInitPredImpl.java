
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

package net.sourceforge.czt.oz.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;

import net.sourceforge.czt.oz.visitor.PromotedInitPredVisitor;

/**
 * An implementation of the interface
 * {@link PromotedInitPred}.
 *
 * @author Gnast version 0.1
 */
public class PromotedInitPredImpl
  extends PredImpl   implements PromotedInitPred
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.oz.ast.OzFactory object factory}.
   */
  protected PromotedInitPredImpl()
  {
  }

  /**
   * Compares the specified object with this PromotedInitPredImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) PromotedInitPredImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        PromotedInitPredImpl object = (PromotedInitPredImpl) obj;
        if (expr_ != null) {
          if (!expr_.equals(object.expr_)) {
            return false;
          }
        }
        else {
          if (object.expr_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this PromotedInitPredImpl.
   * The hash code of a PromotedInitPredImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "PromotedInitPredImpl".hashCode();
    if (expr_ != null) {
      hashCode += constant * expr_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof PromotedInitPredVisitor) {
      PromotedInitPredVisitor visitor = (PromotedInitPredVisitor) v;
      return visitor.visitPromotedInitPred(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    PromotedInitPred zedObject = null;
    try {
      net.sourceforge.czt.z.ast.Expr expr = (net.sourceforge.czt.z.ast.Expr) args[0];
      zedObject = new PromotedInitPredImpl();
      zedObject.setExpr(expr);
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
    Object[] erg = { getExpr() };
    return erg;
  }

  private net.sourceforge.czt.z.ast.Expr expr_;

  public net.sourceforge.czt.z.ast.Expr getExpr()
  {
    return expr_;
  }

  public void setExpr(net.sourceforge.czt.z.ast.Expr expr)
  {
    expr_ = expr;
  }
}
