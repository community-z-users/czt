
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

import net.sourceforge.czt.zed.impl.*;
import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.core.visitor.*;

import net.sourceforge.czt.core.visitor.OptempParaVisitor;

/**
 * An implementation of the interface
 * {@link OptempPara}.
 *
 * @author Gnast version 0.1
 */
public class OptempParaImpl
extends ParaImpl implements OptempPara
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link CoreFactory object factory}.
   */
  protected OptempParaImpl() { }

  /**
   * Compares the specified object with this OptempParaImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) OptempParaImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if(obj != null &&
       this.getClass().equals(obj.getClass()) &&
       super.equals(obj)) {
      OptempParaImpl object = (OptempParaImpl) obj;
      if((mWordOrOperand == null && object.mWordOrOperand != null) ||
         (mWordOrOperand != null &&
         ! mWordOrOperand.equals(object.mWordOrOperand))) return false;
      if(mWordOrOperand == null && object.mWordOrOperand != null)
        return false;
      if((mCat == null && object.mCat != null) ||
         (mCat != null &&
         ! mCat.equals(object.mCat))) return false;
      if(mCat == null && object.mCat != null)
        return false;
      if((mAssoc == null && object.mAssoc != null) ||
         (mAssoc != null &&
         ! mAssoc.equals(object.mAssoc))) return false;
      if(mAssoc == null && object.mAssoc != null)
        return false;
      if((mPrec == null && object.mPrec != null) ||
         (mPrec != null &&
         ! mPrec.equals(object.mPrec))) return false;
      if(mPrec == null && object.mPrec != null)
        return false;
      return true;
    }
    return false;
  }

  /**
   * Returns the hash code value for this OptempParaImpl.
   * The hash code of a OptempParaImpl is defined to be
   * the result of the following calculation:
   *
   * @czt.todo Write the calculation procedure for method hashCode().
   */
  public int hashCode()
  {
    int hashCode = super.hashCode();
    hashCode += "OptempParaImpl".hashCode();
    if(mWordOrOperand != null) {
      hashCode += 31*mWordOrOperand.hashCode();
    }
    if(mCat != null) {
      hashCode += 31*mCat.hashCode();
    }
    if(mAssoc != null) {
      hashCode += 31*mAssoc.hashCode();
    }
    if(mPrec != null) {
      hashCode += 31*mPrec.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof OptempParaVisitor)
    {
      OptempParaVisitor visitor = (OptempParaVisitor) v;
      return visitor.visitOptempPara(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.zed.ast.Term create(Object[] args) {
    OptempPara zedObject = null;
    try {
      java.util.List wordOrOperand = (java.util.List) args[0];
      Cat cat = (Cat) args[1];
      Assoc assoc = (Assoc) args[2];
      Integer prec = (Integer) args[3];
      zedObject = new OptempParaImpl();
      if(wordOrOperand != null) {
        zedObject.getWordOrOperand().addAll(wordOrOperand);
      }
      zedObject.setCat(cat);
      zedObject.setAssoc(assoc);
      zedObject.setPrec(prec);
    } catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    } catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getWordOrOperand(), getCat(), getAssoc(), getPrec() };
    return erg;
  }

  private java.util.List mWordOrOperand = new java.util.Vector();

  public java.util.List getWordOrOperand()
  {
    return mWordOrOperand;
  }

  private Cat mCat;

  public Cat getCat()
  {
    return mCat;
  }

  public void setCat(Cat cat)
  {
    mCat = cat;
  }

  private Assoc mAssoc;

  public Assoc getAssoc()
  {
    return mAssoc;
  }

  public void setAssoc(Assoc assoc)
  {
    mAssoc = assoc;
  }

  private Integer mPrec;

  public Integer getPrec()
  {
    return mPrec;
  }

  public void setPrec(Integer prec)
  {
    mPrec = prec;
  }
}
