
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

package net.sourceforge.czt.oz.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;

import net.sourceforge.czt.oz.visitor.StateVisitor;

/**
 * An implementation of the interface
 * {@link State}.
 *
 * @author Gnast version 0.1
 */
public class StateImpl
  extends TermAImpl   implements State
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.oz.ast.OzFactory object factory}.
   */
  protected StateImpl()
  {
  }

  /**
   * Compares the specified object with this StateImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) StateImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        StateImpl object = (StateImpl) obj;
        if (primaryDecl_ != null) {
          if (!primaryDecl_.equals(object.primaryDecl_)) {
            return false;
          }
        }
        else {
          if (object.primaryDecl_ != null) {
            return false;
          }
        }
        if (secondaryDecl_ != null) {
          if (!secondaryDecl_.equals(object.secondaryDecl_)) {
            return false;
          }
        }
        else {
          if (object.secondaryDecl_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this StateImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "StateImpl".hashCode();
    if (primaryDecl_ != null) {
      hashCode += constant * primaryDecl_.hashCode();
    }
    if (secondaryDecl_ != null) {
      hashCode += constant * secondaryDecl_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof StateVisitor) {
      StateVisitor visitor = (StateVisitor) v;
      return visitor.visitState(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    State zedObject = null;
    try {
      java.util.List primaryDecl = (java.util.List) args[0];
      java.util.List secondaryDecl = (java.util.List) args[1];
      zedObject = new StateImpl();
      if (primaryDecl != null) {
        zedObject.getPrimaryDecl().addAll(primaryDecl);
      }
      if (secondaryDecl != null) {
        zedObject.getSecondaryDecl().addAll(secondaryDecl);
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
    Object[] erg = { getPrimaryDecl(), getSecondaryDecl() };
    return erg;
  }


  private net.sourceforge.czt.base.ast.ListTerm primaryDecl_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(PrimaryDecl.class);

  public net.sourceforge.czt.base.ast.ListTerm getPrimaryDecl()
  {
    return primaryDecl_;
  }


  private net.sourceforge.czt.base.ast.ListTerm secondaryDecl_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(SecondaryDecl.class);

  public net.sourceforge.czt.base.ast.ListTerm getSecondaryDecl()
  {
    return secondaryDecl_;
  }
}
