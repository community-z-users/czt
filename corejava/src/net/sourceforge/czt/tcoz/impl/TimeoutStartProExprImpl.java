
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

import net.sourceforge.czt.tcoz.visitor.TimeoutStartProExprVisitor;

/**
 * An implementation of the interface
 * {@link TimeoutStartProExpr}.
 *
 * @author Gnast version 0.1
 */
public class TimeoutStartProExprImpl
  extends OperationExprImpl   implements TimeoutStartProExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.tcoz.ast.TcozFactory object factory}.
   */
  protected TimeoutStartProExprImpl()
  {
  }

  /**
   * Compares the specified object with this TimeoutStartProExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) TimeoutStartProExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        TimeoutStartProExprImpl object = (TimeoutStartProExprImpl) obj;
        if (normalOp_ != null) {
          if (!normalOp_.equals(object.normalOp_)) {
            return false;
          }
        }
        else {
          if (object.normalOp_ != null) {
            return false;
          }
        }
        if (intOrTimeout_ != null) {
          if (!intOrTimeout_.equals(object.intOrTimeout_)) {
            return false;
          }
        }
        else {
          if (object.intOrTimeout_ != null) {
            return false;
          }
        }
        if (handlerOp_ != null) {
          if (!handlerOp_.equals(object.handlerOp_)) {
            return false;
          }
        }
        else {
          if (object.handlerOp_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this TimeoutStartProExprImpl.
   * The hash code of a TimeoutStartProExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "TimeoutStartProExprImpl".hashCode();
    if (normalOp_ != null) {
      hashCode += constant * normalOp_.hashCode();
    }
    if (intOrTimeout_ != null) {
      hashCode += constant * intOrTimeout_.hashCode();
    }
    if (handlerOp_ != null) {
      hashCode += constant * handlerOp_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof TimeoutStartProExprVisitor) {
      TimeoutStartProExprVisitor visitor = (TimeoutStartProExprVisitor) v;
      return visitor.visitTimeoutStartProExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    TimeoutStartProExpr zedObject = null;
    try {
      net.sourceforge.czt.oz.ast.OperationExpr normalOp = (net.sourceforge.czt.oz.ast.OperationExpr) args[0];
      net.sourceforge.czt.z.ast.Expr1 intOrTimeout = (net.sourceforge.czt.z.ast.Expr1) args[1];
      net.sourceforge.czt.oz.ast.OperationExpr handlerOp = (net.sourceforge.czt.oz.ast.OperationExpr) args[2];
      zedObject = new TimeoutStartProExprImpl();
      zedObject.setNormalOp(normalOp);
      zedObject.setIntOrTimeout(intOrTimeout);
      zedObject.setHandlerOp(handlerOp);
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
    Object[] erg = { getNormalOp(), getIntOrTimeout(), getHandlerOp() };
    return erg;
  }

  private net.sourceforge.czt.oz.ast.OperationExpr normalOp_;

  public net.sourceforge.czt.oz.ast.OperationExpr getNormalOp()
  {
    return normalOp_;
  }

  public void setNormalOp(net.sourceforge.czt.oz.ast.OperationExpr normalOp)
  {
    normalOp_ = normalOp;
  }

  private net.sourceforge.czt.z.ast.Expr1 intOrTimeout_;

  public net.sourceforge.czt.z.ast.Expr1 getIntOrTimeout()
  {
    return intOrTimeout_;
  }

  public void setIntOrTimeout(net.sourceforge.czt.z.ast.Expr1 intOrTimeout)
  {
    intOrTimeout_ = intOrTimeout;
  }

  private net.sourceforge.czt.oz.ast.OperationExpr handlerOp_;

  public net.sourceforge.czt.oz.ast.OperationExpr getHandlerOp()
  {
    return handlerOp_;
  }

  public void setHandlerOp(net.sourceforge.czt.oz.ast.OperationExpr handlerOp)
  {
    handlerOp_ = handlerOp;
  }
}
