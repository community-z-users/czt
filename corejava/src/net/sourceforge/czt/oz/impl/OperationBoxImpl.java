
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

import net.sourceforge.czt.oz.visitor.OperationBoxVisitor;

/**
 * An implementation of the interface
 * {@link OperationBox}.
 *
 * @author Gnast version 0.1
 */
public class OperationBoxImpl
  extends OperationBoxExprImpl   implements OperationBox
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.oz.ast.OzFactory object factory}.
   */
  protected OperationBoxImpl()
  {
  }

  /**
   * Compares the specified object with this OperationBoxImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) OperationBoxImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        OperationBoxImpl object = (OperationBoxImpl) obj;
        if (deltaList_ != null) {
          if (!deltaList_.equals(object.deltaList_)) {
            return false;
          }
        }
        else {
          if (object.deltaList_ != null) {
            return false;
          }
        }
        if (decl_ != null) {
          if (!decl_.equals(object.decl_)) {
            return false;
          }
        }
        else {
          if (object.decl_ != null) {
            return false;
          }
        }
        if (pred_ != null) {
          if (!pred_.equals(object.pred_)) {
            return false;
          }
        }
        else {
          if (object.pred_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this OperationBoxImpl.
   * The hash code of a OperationBoxImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "OperationBoxImpl".hashCode();
    if (deltaList_ != null) {
      hashCode += constant * deltaList_.hashCode();
    }
    if (decl_ != null) {
      hashCode += constant * decl_.hashCode();
    }
    if (pred_ != null) {
      hashCode += constant * pred_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof OperationBoxVisitor) {
      OperationBoxVisitor visitor = (OperationBoxVisitor) v;
      return visitor.visitOperationBox(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    OperationBox zedObject = null;
    try {
      RefNameList deltaList = (RefNameList) args[0];
      java.util.List decl = (java.util.List) args[1];
      java.util.List pred = (java.util.List) args[2];
      zedObject = new OperationBoxImpl();
      zedObject.setDeltaList(deltaList);
      if (decl != null) {
        zedObject.getDecl().addAll(decl);
      }
      if (pred != null) {
        zedObject.getPred().addAll(pred);
      }
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
    Object[] erg = { getDeltaList(), getDecl(), getPred() };
    return erg;
  }

  private RefNameList deltaList_;

  public RefNameList getDeltaList()
  {
    return deltaList_;
  }

  public void setDeltaList(RefNameList deltaList)
  {
    deltaList_ = deltaList;
  }


  private java.util.List decl_ =
    new TypesafeList(net.sourceforge.czt.z.ast.Decl.class);

  public java.util.List getDecl()
  {
    return decl_;
  }


  private java.util.List pred_ =
    new TypesafeList(net.sourceforge.czt.z.ast.Pred.class);

  public java.util.List getPred()
  {
    return pred_;
  }
}
