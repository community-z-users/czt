
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

import net.sourceforge.czt.oz.visitor.RenameOpExprVisitor;

/**
 * An implementation of the interface
 * {@link RenameOpExpr}.
 *
 * @author Gnast version 0.1
 */
public class RenameOpExprImpl
  extends OperationExprImpl   implements RenameOpExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.oz.ast.OzFactory object factory}.
   */
  protected RenameOpExprImpl()
  {
  }

  /**
   * Compares the specified object with this RenameOpExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) RenameOpExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        RenameOpExprImpl object = (RenameOpExprImpl) obj;
        if (operationExpr_ != null) {
          if (!operationExpr_.equals(object.operationExpr_)) {
            return false;
          }
        }
        else {
          if (object.operationExpr_ != null) {
            return false;
          }
        }
        if (renameExpr_ != null) {
          if (!renameExpr_.equals(object.renameExpr_)) {
            return false;
          }
        }
        else {
          if (object.renameExpr_ != null) {
            return false;
          }
        }
        return true;
      }
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
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "RenameOpExprImpl".hashCode();
    if (operationExpr_ != null) {
      hashCode += constant * operationExpr_.hashCode();
    }
    if (renameExpr_ != null) {
      hashCode += constant * renameExpr_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof RenameOpExprVisitor) {
      RenameOpExprVisitor visitor = (RenameOpExprVisitor) v;
      return visitor.visitRenameOpExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    RenameOpExpr zedObject = null;
    try {
      OperationExpr operationExpr = (OperationExpr) args[0];
      net.sourceforge.czt.z.ast.RenameExpr renameExpr = (net.sourceforge.czt.z.ast.RenameExpr) args[1];
      zedObject = new RenameOpExprImpl();
      zedObject.setOperationExpr(operationExpr);
      zedObject.setRenameExpr(renameExpr);
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
    Object[] erg = { getOperationExpr(), getRenameExpr() };
    return erg;
  }

  private OperationExpr operationExpr_;

  public OperationExpr getOperationExpr()
  {
    return operationExpr_;
  }

  public void setOperationExpr(OperationExpr operationExpr)
  {
    operationExpr_ = operationExpr;
  }

  private net.sourceforge.czt.z.ast.RenameExpr renameExpr_;

  public net.sourceforge.czt.z.ast.RenameExpr getRenameExpr()
  {
    return renameExpr_;
  }

  public void setRenameExpr(net.sourceforge.czt.z.ast.RenameExpr renameExpr)
  {
    renameExpr_ = renameExpr;
  }
}
