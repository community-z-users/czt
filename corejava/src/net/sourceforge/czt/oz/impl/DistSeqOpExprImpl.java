
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

package net.sourceforge.czt.oz.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;

import net.sourceforge.czt.oz.visitor.DistSeqOpExprVisitor;

/**
 * An implementation of the interface
 * {@link DistSeqOpExpr}.
 *
 * @author Gnast version 0.1
 */
public class DistSeqOpExprImpl
  extends DistOpExprImpl   implements DistSeqOpExpr
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.oz.ast.OzFactory object factory}.
   */
  protected DistSeqOpExprImpl()
  {
  }

  /**
   * Compares the specified object with this DistSeqOpExprImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) DistSeqOpExprImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        DistSeqOpExprImpl object = (DistSeqOpExprImpl) obj;
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this DistSeqOpExprImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "DistSeqOpExprImpl".hashCode();
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof DistSeqOpExprVisitor) {
      DistSeqOpExprVisitor visitor = (DistSeqOpExprVisitor) v;
      return visitor.visitDistSeqOpExpr(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    DistSeqOpExpr zedObject = null;
    try {
      net.sourceforge.czt.z.ast.SchText schText = (net.sourceforge.czt.z.ast.SchText) args[0];
      OpExpr opExpr = (OpExpr) args[1];
      zedObject = new DistSeqOpExprImpl();
      zedObject.setSchText(schText);
      zedObject.setOpExpr(opExpr);
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
    Object[] erg = { getSchText(), getOpExpr() };
    return erg;
  }
}
