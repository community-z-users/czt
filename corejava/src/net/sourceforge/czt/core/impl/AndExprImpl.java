
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

package net.sourceforge.czt.core.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.zed.impl.*;
import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.core.visitor.*;

import net.sourceforge.czt.core.visitor.AndExprVisitor;

/**
 * An implementation of the interface
 * {@link AndExpr}.
 *
 * @author Gnast version 0.1
 */
public class AndExprImpl
extends SchExpr2Impl implements AndExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link CoreFactory object factory}.
   */
  protected AndExprImpl() { }

  /**
   * Compares the specified object with this AndExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) AndExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      AndExprImpl object = (AndExprImpl) obj;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this AndExprImpl.
   * The hash code of a AndExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "AndExprImpl".hashCode();
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof AndExprVisitor)
    {
      AndExprVisitor visitor = (AndExprVisitor) v;
      return visitor.visitAndExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.zed.ast.Term create(Object[] args) {
    AndExpr zedObject = null;
    try {
      Expr leftExpr = (Expr) args[0];
      Expr rightExpr = (Expr) args[1];
      zedObject = new AndExprImpl();
      zedObject.setLeftExpr(leftExpr);
      zedObject.setRightExpr(rightExpr);
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getLeftExpr(), getRightExpr() };
    return erg;
  }
}
