
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

package net.sourceforge.czt.z.impl;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z.visitor.OptempParaVisitor;

/**
 * An implementation of the interface
 * {@link OptempPara}.
 *
 * @author Gnast version 0.1
 */
public class OptempParaImpl
  extends ParaImpl   implements OptempPara
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.z.ast.ZFactory object factory}.
   */
  protected OptempParaImpl()
  {
  }

  /**
   * Compares the specified object with this OptempParaImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) OptempParaImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        OptempParaImpl object = (OptempParaImpl) obj;
        if (oper_ != null) {
          if (!oper_.equals(object.oper_)) {
            return false;
          }
        }
        else {
          if (object.oper_ != null) {
            return false;
          }
        }
        if (cat_ != null) {
          if (!cat_.equals(object.cat_)) {
            return false;
          }
        }
        else {
          if (object.cat_ != null) {
            return false;
          }
        }
        if (assoc_ != null) {
          if (!assoc_.equals(object.assoc_)) {
            return false;
          }
        }
        else {
          if (object.assoc_ != null) {
            return false;
          }
        }
        if (prec_ != null) {
          if (!prec_.equals(object.prec_)) {
            return false;
          }
        }
        else {
          if (object.prec_ != null) {
            return false;
          }
        }
        return true;
      }
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
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "OptempParaImpl".hashCode();
    if (oper_ != null) {
      hashCode += constant * oper_.hashCode();
    }
    if (cat_ != null) {
      hashCode += constant * cat_.hashCode();
    }
    if (assoc_ != null) {
      hashCode += constant * assoc_.hashCode();
    }
    if (prec_ != null) {
      hashCode += constant * prec_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof OptempParaVisitor) {
      OptempParaVisitor visitor = (OptempParaVisitor) v;
      return visitor.visitOptempPara(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    OptempPara zedObject = null;
    try {
      java.util.List oper = (java.util.List) args[0];
      Cat cat = (Cat) args[1];
      Assoc assoc = (Assoc) args[2];
      Integer prec = (Integer) args[3];
      zedObject = new OptempParaImpl();
      if (oper != null) {
        zedObject.getOper().addAll(oper);
      }
      zedObject.setCat(cat);
      zedObject.setAssoc(assoc);
      zedObject.setPrec(prec);
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
    Object[] erg = { getOper(), getCat(), getAssoc(), getPrec() };
    return erg;
  }


  private java.util.List oper_ =
    new TypesafeList(Oper.class);

  public java.util.List getOper()
  {
    return oper_;
  }

  private Cat cat_;

  public Cat getCat()
  {
    return cat_;
  }

  public void setCat(Cat cat)
  {
    cat_ = cat;
  }

  private Assoc assoc_;

  public Assoc getAssoc()
  {
    return assoc_;
  }

  public void setAssoc(Assoc assoc)
  {
    assoc_ = assoc;
  }

  private Integer prec_;

  public Integer getPrec()
  {
    return prec_;
  }

  public void setPrec(Integer prec)
  {
    prec_ = prec;
  }
}
