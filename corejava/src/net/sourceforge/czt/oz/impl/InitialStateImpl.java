
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

import net.sourceforge.czt.oz.visitor.InitialStateVisitor;

/**
 * An implementation of the interface
 * {@link InitialState}.
 *
 * @author Gnast version 0.1
 */
public class InitialStateImpl
extends TermAImpl implements InitialState
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link OZFactory object factory}.
   */
  protected InitialStateImpl() { }

  /**
   * Compares the specified object with this InitialStateImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) InitialStateImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      InitialStateImpl object = (InitialStateImpl) obj;
      if((mPred == null && object.mPred != null) ||
         (mPred != null &&
         ! mPred.equals(object.mPred))) return false;
      if(mPred == null && object.mPred != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this InitialStateImpl.
   * The hash code of a InitialStateImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "InitialStateImpl".hashCode();
    if(mPred != null) {
      hashCode += 31*mPred.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof InitialStateVisitor)
    {
      InitialStateVisitor visitor = (InitialStateVisitor) v;
      return visitor.visitInitialState(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.zed.ast.Term create(Object[] args) {
    InitialState zedObject = null;
    try {
      java.util.List pred = (java.util.List) args[0];
      zedObject = new InitialStateImpl();
      if(pred != null) {
        zedObject.getPred().addAll(pred);
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
    Object[] erg = { getPred() };
    return erg;
  }

  private java.util.List mPred = new java.util.Vector();

  public java.util.List getPred()
  {
    return mPred;
  }
}
