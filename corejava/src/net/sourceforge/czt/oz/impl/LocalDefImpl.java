
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

import net.sourceforge.czt.oz.visitor.LocalDefVisitor;

/**
 * An implementation of the interface
 * {@link LocalDef}.
 *
 * @author Gnast version 0.1
 */
public class LocalDefImpl
extends TermAImpl implements LocalDef
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link OZFactory object factory}.
   */
  protected LocalDefImpl() { }

  /**
   * Compares the specified object with this LocalDefImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) LocalDefImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      LocalDefImpl object = (LocalDefImpl) obj;
      if((mGivenPara == null && object.mGivenPara != null) ||
         (mGivenPara != null &&
         ! mGivenPara.equals(object.mGivenPara))) return false;
      if(mGivenPara == null && object.mGivenPara != null)
        return false;
      if((mAxPara == null && object.mAxPara != null) ||
         (mAxPara != null &&
         ! mAxPara.equals(object.mAxPara))) return false;
      if(mAxPara == null && object.mAxPara != null)
        return false;
      if((mFreePara == null && object.mFreePara != null) ||
         (mFreePara != null &&
         ! mFreePara.equals(object.mFreePara))) return false;
      if(mFreePara == null && object.mFreePara != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this LocalDefImpl.
   * The hash code of a LocalDefImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "LocalDefImpl".hashCode();
    if(mGivenPara != null) {
      hashCode += 31*mGivenPara.hashCode();
    }
    if(mAxPara != null) {
      hashCode += 31*mAxPara.hashCode();
    }
    if(mFreePara != null) {
      hashCode += 31*mFreePara.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof LocalDefVisitor)
    {
      LocalDefVisitor visitor = (LocalDefVisitor) v;
      return visitor.visitLocalDef(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.zed.ast.Term create(Object[] args) {
    LocalDef zedObject = null;
    try {
      java.util.List givenPara = (java.util.List) args[0];
      java.util.List axPara = (java.util.List) args[1];
      java.util.List freePara = (java.util.List) args[2];
      zedObject = new LocalDefImpl();
      if(givenPara != null) {
        zedObject.getGivenPara().addAll(givenPara);
      }
      if(axPara != null) {
        zedObject.getAxPara().addAll(axPara);
      }
      if(freePara != null) {
        zedObject.getFreePara().addAll(freePara);
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
    Object[] erg = { getGivenPara(), getAxPara(), getFreePara() };
    return erg;
  }

  private java.util.List mGivenPara = new java.util.Vector();

  public java.util.List getGivenPara()
  {
    return mGivenPara;
  }

  private java.util.List mAxPara = new java.util.Vector();

  public java.util.List getAxPara()
  {
    return mAxPara;
  }

  private java.util.List mFreePara = new java.util.Vector();

  public java.util.List getFreePara()
  {
    return mFreePara;
  }
}
