
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

import net.sourceforge.czt.oz.visitor.MainOpExprVisitor;

/**
 * An implementation of the interface
 * {@link MainOpExpr}.
 *
 * @author Gnast version 0.1
 */
public class MainOpExprImpl
extends TermAImpl implements MainOpExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link OZFactory object factory}.
   */
  protected MainOpExprImpl() { }

  /**
   * Compares the specified object with this MainOpExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) MainOpExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      MainOpExprImpl object = (MainOpExprImpl) obj;
      if((mSchText == null && object.mSchText != null) ||
         (mSchText != null &&
         ! mSchText.equals(object.mSchText))) return false;
      if(mSchText == null && object.mSchText != null)
        return false;
      if((mOperationExpr == null && object.mOperationExpr != null) ||
         (mOperationExpr != null &&
         ! mOperationExpr.equals(object.mOperationExpr))) return false;
      if(mOperationExpr == null && object.mOperationExpr != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this MainOpExprImpl.
   * The hash code of a MainOpExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "MainOpExprImpl".hashCode();
    if(mSchText != null) {
      hashCode += 31*mSchText.hashCode();
    }
    if(mOperationExpr != null) {
      hashCode += 31*mOperationExpr.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof MainOpExprVisitor)
    {
      MainOpExprVisitor visitor = (MainOpExprVisitor) v;
      return visitor.visitMainOpExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.zed.ast.Term create(Object[] args) {
    MainOpExpr zedObject = null;
    try {
      net.sourceforge.czt.core.ast.SchText schText = (net.sourceforge.czt.core.ast.SchText) args[0];
      OperationExpr operationExpr = (OperationExpr) args[1];
      zedObject = new MainOpExprImpl();
      zedObject.setSchText(schText);
      zedObject.setOperationExpr(operationExpr);
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getSchText(), getOperationExpr() };
    return erg;
  }

  private net.sourceforge.czt.core.ast.SchText mSchText;

  public net.sourceforge.czt.core.ast.SchText getSchText()
  {
    return mSchText;
  }

  public void setSchText(net.sourceforge.czt.core.ast.SchText schText)
  {
    mSchText = schText;
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
}
