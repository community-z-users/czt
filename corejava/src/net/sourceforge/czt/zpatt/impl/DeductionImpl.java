
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

import net.sourceforge.czt.zpatt.visitor.DeductionVisitor;

/**
 * An implementation of the interface
 * {@link Deduction}.
 *
 * @author Gnast version 0.1
 */
public class DeductionImpl
  extends TermAImpl   implements Deduction
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.zpatt.ast.ZpattFactory object factory}.
   */
  protected DeductionImpl()
  {
  }

  /**
   * Compares the specified object with this DeductionImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) DeductionImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        DeductionImpl object = (DeductionImpl) obj;
        if (binding_ != null) {
          if (!binding_.equals(object.binding_)) {
            return false;
          }
        }
        else {
          if (object.binding_ != null) {
            return false;
          }
        }
        if (sequent_ != null) {
          if (!sequent_.equals(object.sequent_)) {
            return false;
          }
        }
        else {
          if (object.sequent_ != null) {
            return false;
          }
        }
        if (name_ != null) {
          if (!name_.equals(object.name_)) {
            return false;
          }
        }
        else {
          if (object.name_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this DeductionImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "DeductionImpl".hashCode();
    if (binding_ != null) {
      hashCode += constant * binding_.hashCode();
    }
    if (sequent_ != null) {
      hashCode += constant * sequent_.hashCode();
    }
    if (name_ != null) {
      hashCode += constant * name_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof DeductionVisitor) {
      DeductionVisitor visitor = (DeductionVisitor) v;
      return visitor.visitDeduction(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    Deduction zedObject = null;
    try {
      java.util.List binding = (java.util.List) args[0];
      java.util.List sequent = (java.util.List) args[1];
      String name = (String) args[2];
      zedObject = new DeductionImpl();
      if (binding != null) {
        zedObject.getBinding().addAll(binding);
      }
      if (sequent != null) {
        zedObject.getSequent().addAll(sequent);
      }
      zedObject.setName(name);
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
    Object[] erg = { getBinding(), getSequent(), getName() };
    return erg;
  }


  private net.sourceforge.czt.base.ast.ListTerm binding_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(Binding.class);

  public net.sourceforge.czt.base.ast.ListTerm getBinding()
  {
    return binding_;
  }


  private net.sourceforge.czt.base.ast.ListTerm sequent_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(Sequent.class);

  public net.sourceforge.czt.base.ast.ListTerm getSequent()
  {
    return sequent_;
  }

  private String name_;

  public String getName()
  {
    return name_;
  }

  public void setName(String name)
  {
    name_ = name;
  }
}
