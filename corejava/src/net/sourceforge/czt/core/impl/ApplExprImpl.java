
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

import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.core.util.*;

/**
 * An implementation of the interface
 * {@link ApplExpr}.
 *
 * @author Gnast version 0.1
 */
public class ApplExprImpl
extends Expr2Impl implements ApplExpr
{
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.core.impl.ApplExprImpl");

  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link CoreFactory object factory}.
   */
  protected ApplExprImpl() { }
 
  /**
   * Compares the specified object with this ApplExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ApplExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      ApplExprImpl object = (ApplExprImpl) obj;
      if(mMixfix !=null &&
         ! mMixfix.equals(object.mMixfix)) return false;
      if(mMixfix == null && object.mMixfix != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this ApplExprImpl.
   * The hash code of a ApplExprImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "ApplExprImpl".hashCode();
    if(mMixfix != null) {
      hashCode += 31*mMixfix.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(AstVisitor v) {
    return v.visitApplExpr(this);
  }

  /**
   * Returns a new object of this class.
   */
  public Term create(Object[] args) {
    sLogger.entering("ApplExprImpl", "create", args);
    ApplExpr zedObject = null;
    try {
      Boolean mixfix = (Boolean) args[0];
      java.util.List expr = (java.util.List) args[1];
      zedObject = new ApplExprImpl();
      zedObject.setMixfix(mixfix);
      if(expr != null) {
        zedObject.getExpr().addAll(expr);
      }
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    sLogger.entering("ApplExprImpl", "create", zedObject);
    return zedObject;
  }

  public Object[] getChildren()
  {
    sLogger.entering("ApplExprImpl", "getChildren");
    Object[] erg = { getMixfix(), getExpr() };
    sLogger.exiting("ApplExprImpl", "getChildren", erg);
    return erg;
  }

  private Boolean mMixfix;

  public Boolean getMixfix()
  {
    return mMixfix;
  }

  public void setMixfix(Boolean mixfix)
  {
    mMixfix = mixfix;
  }
}
