
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

package net.sourceforge.czt.zpatt.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

import net.sourceforge.czt.zpatt.visitor.TransformListVisitor;

/**
 * An implementation of the interface
 * {@link TransformList}.
 *
 * @author Gnast version 0.1
 */
public class TransformListImpl
  extends TermImpl   implements TransformList
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.zpatt.ast.ZpattFactory object factory}.
   */
  protected TransformListImpl()
  {
  }

  /**
   * Compares the specified object with this TransformListImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) TransformListImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        TransformListImpl object = (TransformListImpl) obj;
        if (transform_ != null) {
          if (!transform_.equals(object.transform_)) {
            return false;
          }
        }
        else {
          if (object.transform_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this TransformListImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "TransformListImpl".hashCode();
    if (transform_ != null) {
      hashCode += constant * transform_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof TransformListVisitor) {
      TransformListVisitor visitor = (TransformListVisitor) v;
      return visitor.visitTransformList(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    TransformList zedObject = null;
    try {
      java.util.List transform = (java.util.List) args[0];
      zedObject = new TransformListImpl();
      if (transform != null) {
        zedObject.getTransform().addAll(transform);
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
    Object[] erg = { getTransform() };
    return erg;
  }


  private net.sourceforge.czt.base.ast.ListTerm transform_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(Transform.class);

  public net.sourceforge.czt.base.ast.ListTerm getTransform()
  {
    return transform_;
  }
}
