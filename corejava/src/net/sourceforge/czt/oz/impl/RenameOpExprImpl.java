
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

import net.sourceforge.czt.zed.impl.*;
import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.core.impl.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;

import net.sourceforge.czt.oz.visitor.RenameOpExprVisitor;

/**
 * An implementation of the interface
 * {@link RenameOpExpr}.
 *
 * @author Gnast version 0.1
 */
public class RenameOpExprImpl
extends OperationExprImpl implements RenameOpExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link OZFactory object factory}.
   */
  protected RenameOpExprImpl() { }

  /**
   * Compares the specified object with this RenameOpExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) RenameOpExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      RenameOpExprImpl object = (RenameOpExprImpl) obj;
      if((mOperationExpr == null && object.mOperationExpr != null) ||
         (mOperationExpr != null &&
         ! mOperationExpr.equals(object.mOperationExpr))) return false;
      if(mOperationExpr == null && object.mOperationExpr != null)
        return false;
      if((mRenameList == null && object.mRenameList != null) ||
         (mRenameList != null &&
         ! mRenameList.equals(object.mRenameList))) return false;
      if(mRenameList == null && object.mRenameList != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this RenameOpExprImpl.
   * The hash code of a RenameOpExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "RenameOpExprImpl".hashCode();
    if(mOperationExpr != null) {
      hashCode += 31*mOperationExpr.hashCode();
    }
    if(mRenameList != null) {
      hashCode += 31*mRenameList.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof RenameOpExprVisitor)
    {
      RenameOpExprVisitor visitor = (RenameOpExprVisitor) v;
      return visitor.visitRenameOpExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.zed.ast.Term create(Object[] args) {
    RenameOpExpr zedObject = null;
    try {
      OperationExpr operationExpr = (OperationExpr) args[0];
      RenameList renameList = (RenameList) args[1];
      zedObject = new RenameOpExprImpl();
      zedObject.setOperationExpr(operationExpr);
      zedObject.setRenameList(renameList);
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getOperationExpr(), getRenameList() };
    return erg;
  }

  private OperationExpr mOperationExpr;

  public OperationExpr getOperationExpr()
  {
    return mOperationExpr;
  }

  public void setOperationExpr(OperationExpr operationExpr)
  {
    mOperationExpr = operationExpr;
  }

  private RenameList mRenameList;

  public RenameList getRenameList()
  {
    return mRenameList;
  }

  public void setRenameList(RenameList renameList)
  {
    mRenameList = renameList;
  }
}
