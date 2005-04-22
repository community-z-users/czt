
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstClass.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004, 2005 Mark Utting
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

package net.sourceforge.czt.zpatt.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

import net.sourceforge.czt.zpatt.visitor.LookupConstDeclProvisoVisitor;

/**
 * An implementation of the interface
 * {@link LookupConstDeclProviso}.
 *
 * @author Gnast version 0.1
 */
public class LookupConstDeclProvisoImpl
  extends LookupProvisoImpl   implements LookupConstDeclProviso
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.zpatt.ast.ZpattFactory object factory}.
   */
  protected LookupConstDeclProvisoImpl()
  {
  }

  /**
   * Compares the specified object with this LookupConstDeclProvisoImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) LookupConstDeclProvisoImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        LookupConstDeclProvisoImpl object = (LookupConstDeclProvisoImpl) obj;
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
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this LookupConstDeclProvisoImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "LookupConstDeclProvisoImpl".hashCode();
    if (leftExpr_ != null) {
      hashCode += constant * leftExpr_.hashCode();
    }
    if (rightExpr_ != null) {
      hashCode += constant * rightExpr_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof LookupConstDeclProvisoVisitor) {
      LookupConstDeclProvisoVisitor visitor = (LookupConstDeclProvisoVisitor) v;
      return visitor.visitLookupConstDeclProviso(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    LookupConstDeclProviso zedObject = null;
    try {
      SequentContext sequentContext = (SequentContext) args[0];
      net.sourceforge.czt.z.ast.Expr leftExpr = (net.sourceforge.czt.z.ast.Expr) args[1];
      net.sourceforge.czt.z.ast.Expr rightExpr = (net.sourceforge.czt.z.ast.Expr) args[2];
      zedObject = new LookupConstDeclProvisoImpl();
      zedObject.setSequentContext(sequentContext);
      zedObject.setLeftExpr(leftExpr);
      zedObject.setRightExpr(rightExpr);
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
    Object[] erg = { getSequentContext(), getLeftExpr(), getRightExpr() };
    return erg;
  }

  private net.sourceforge.czt.z.ast.Expr leftExpr_;

  public net.sourceforge.czt.z.ast.Expr getLeftExpr()
  {
    return leftExpr_;
  }

  public void setLeftExpr(net.sourceforge.czt.z.ast.Expr leftExpr)
  {
    leftExpr_ = leftExpr;
  }

  private net.sourceforge.czt.z.ast.Expr rightExpr_;

  public net.sourceforge.czt.z.ast.Expr getRightExpr()
  {
    return rightExpr_;
  }

  public void setRightExpr(net.sourceforge.czt.z.ast.Expr rightExpr)
  {
    rightExpr_ = rightExpr;
  }
}
