
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

import net.sourceforge.czt.zpatt.visitor.JokerPredBindingVisitor;

/**
 * An implementation of the interface
 * {@link JokerPredBinding}.
 *
 * @author Gnast version 0.1
 */
public class JokerPredBindingImpl
  extends BindingImpl   implements JokerPredBinding
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.zpatt.ast.ZpattFactory object factory}.
   */
  protected JokerPredBindingImpl()
  {
  }

  /**
   * Compares the specified object with this JokerPredBindingImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) JokerPredBindingImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        JokerPredBindingImpl object = (JokerPredBindingImpl) obj;
        if (jokerPred_ != null) {
          if (!jokerPred_.equals(object.jokerPred_)) {
            return false;
          }
        }
        else {
          if (object.jokerPred_ != null) {
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
   * Returns the hash code value for this JokerPredBindingImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "JokerPredBindingImpl".hashCode();
    if (jokerPred_ != null) {
      hashCode += constant * jokerPred_.hashCode();
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
    if (v instanceof JokerPredBindingVisitor) {
      JokerPredBindingVisitor visitor = (JokerPredBindingVisitor) v;
      return visitor.visitJokerPredBinding(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    JokerPredBinding zedObject = null;
    try {
      JokerPred jokerPred = (JokerPred) args[0];
      net.sourceforge.czt.z.ast.Pred pred = (net.sourceforge.czt.z.ast.Pred) args[1];
      zedObject = new JokerPredBindingImpl();
      zedObject.setJokerPred(jokerPred);
      zedObject.setPred(pred);
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
    Object[] erg = { getJokerPred(), getPred() };
    return erg;
  }

  private JokerPred jokerPred_;

  public JokerPred getJokerPred()
  {
    return jokerPred_;
  }

  public void setJokerPred(JokerPred jokerPred)
  {
    jokerPred_ = jokerPred;
  }

  private net.sourceforge.czt.z.ast.Pred pred_;

  public net.sourceforge.czt.z.ast.Pred getPred()
  {
    return pred_;
  }

  public void setPred(net.sourceforge.czt.z.ast.Pred pred)
  {
    pred_ = pred;
  }
}
