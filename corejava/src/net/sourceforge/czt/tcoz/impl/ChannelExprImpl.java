
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

import net.sourceforge.czt.tcoz.visitor.ChannelExprVisitor;

/**
 * An implementation of the interface
 * {@link ChannelExpr}.
 *
 * @author Gnast version 0.1
 */
public class ChannelExprImpl
  extends ExprImpl   implements ChannelExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.tcoz.ast.TcozFactory object factory}.
   */
  protected ChannelExprImpl()
  {
  }

  /**
   * Compares the specified object with this ChannelExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ChannelExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        ChannelExprImpl object = (ChannelExprImpl) obj;
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
        if (channelType_ != null) {
          if (!channelType_.equals(object.channelType_)) {
            return false;
          }
        }
        else {
          if (object.channelType_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this ChannelExprImpl.
   * The hash code of a ChannelExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ChannelExprImpl".hashCode();
    if (expr_ != null) {
      hashCode += constant * expr_.hashCode();
    }
    if (channelType_ != null) {
      hashCode += constant * channelType_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof ChannelExprVisitor) {
      ChannelExprVisitor visitor = (ChannelExprVisitor) v;
      return visitor.visitChannelExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    ChannelExpr zedObject = null;
    try {
      net.sourceforge.czt.z.ast.Expr expr = (net.sourceforge.czt.z.ast.Expr) args[0];
      ChannelType channelType = (ChannelType) args[1];
      zedObject = new ChannelExprImpl();
      zedObject.setExpr(expr);
      zedObject.setChannelType(channelType);
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
    Object[] erg = { getExpr(), getChannelType() };
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

  private ChannelType channelType_;

  public ChannelType getChannelType()
  {
    return channelType_;
  }

  public void setChannelType(ChannelType channelType)
  {
    channelType_ = channelType;
  }
}
