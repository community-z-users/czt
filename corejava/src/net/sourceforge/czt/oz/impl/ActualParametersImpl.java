
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

import net.sourceforge.czt.oz.visitor.ActualParametersVisitor;

/**
 * An implementation of the interface
 * {@link ActualParameters}.
 *
 * @author Gnast version 0.1
 */
public class ActualParametersImpl
extends TermAImpl implements ActualParameters
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link OZFactory object factory}.
   */
  protected ActualParametersImpl() { }

  /**
   * Compares the specified object with this ActualParametersImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ActualParametersImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      ActualParametersImpl object = (ActualParametersImpl) obj;
      if((mExpr == null && object.mExpr != null) ||
         (mExpr != null &&
         ! mExpr.equals(object.mExpr))) return false;
      if(mExpr == null && object.mExpr != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this ActualParametersImpl.
   * The hash code of a ActualParametersImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "ActualParametersImpl".hashCode();
    if(mExpr != null) {
      hashCode += 31*mExpr.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof ActualParametersVisitor)
    {
      ActualParametersVisitor visitor = (ActualParametersVisitor) v;
      return visitor.visitActualParameters(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.zed.ast.Term create(Object[] args) {
    ActualParameters zedObject = null;
    try {
      java.util.List expr = (java.util.List) args[0];
      zedObject = new ActualParametersImpl();
      if(expr != null) {
        zedObject.getExpr().addAll(expr);
      }
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getExpr() };
    return erg;
  }

  private java.util.List mExpr = new java.util.Vector();

  public java.util.List getExpr()
  {
    return mExpr;
  }
}
