
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
 * {@link Expr0N}.
 *
 * @author Gnast version 0.1
 */
public abstract class Expr0NImpl
extends ExprImpl implements Expr0N
{
 
  /**
   * Compares the specified object with this Expr0NImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) Expr0NImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      Expr0NImpl object = (Expr0NImpl) obj;
      if(mExpr !=null &&
         ! mExpr.equals(object.mExpr)) return false;
      if(mExpr == null && object.mExpr != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this Expr0NImpl.
   * The hash code of a Expr0NImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "Expr0NImpl".hashCode();
    if(mExpr != null) {
      hashCode += 31*mExpr.hashCode();
    }
    return hashCode;
  }


  private java.util.List mExpr = new java.util.Vector();

  public java.util.List getExpr()
  {
    return mExpr;
  }
}
