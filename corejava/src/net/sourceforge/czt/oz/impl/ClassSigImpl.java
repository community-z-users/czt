
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

import net.sourceforge.czt.oz.visitor.ClassSigVisitor;

/**
 * An implementation of the interface
 * {@link ClassSig}.
 *
 * @author Gnast version 0.1
 */
public class ClassSigImpl
  extends TermImpl   implements ClassSig
{
  /**
   * The default constructor.
   *
   * Do not use it explicitly, unless you are extending this class.
   * If you want to create an instance of this class, please use the
   * {@link net.sourceforge.czt.oz.ast.OzFactory object factory}.
   */
  protected ClassSigImpl()
  {
  }

  /**
   * Compares the specified object with this ClassSigImpl
   * for equality.  Returns true if and only if the specified object is
   * also a(n) ClassSigImpl and all the getter methods except getAnns
   * return equal objects.
   */
  public boolean equals(Object obj)
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
        ClassSigImpl object = (ClassSigImpl) obj;
        if (classes_ != null) {
          if (!classes_.equals(object.classes_)) {
            return false;
          }
        }
        else {
          if (object.classes_ != null) {
            return false;
          }
        }
        if (state_ != null) {
          if (!state_.equals(object.state_)) {
            return false;
          }
        }
        else {
          if (object.state_ != null) {
            return false;
          }
        }
        if (attribute_ != null) {
          if (!attribute_.equals(object.attribute_)) {
            return false;
          }
        }
        else {
          if (object.attribute_ != null) {
            return false;
          }
        }
        if (operation_ != null) {
          if (!operation_.equals(object.operation_)) {
            return false;
          }
        }
        else {
          if (object.operation_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this ClassSigImpl.
   */
  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ClassSigImpl".hashCode();
    if (classes_ != null) {
      hashCode += constant * classes_.hashCode();
    }
    if (state_ != null) {
      hashCode += constant * state_.hashCode();
    }
    if (attribute_ != null) {
      hashCode += constant * attribute_.hashCode();
    }
    if (operation_ != null) {
      hashCode += constant * operation_.hashCode();
    }
    return hashCode;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof ClassSigVisitor) {
      ClassSigVisitor visitor = (ClassSigVisitor) v;
      return visitor.visitClassSig(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    ClassSig zedObject = null;
    try {
      java.util.List classes = (java.util.List) args[0];
      net.sourceforge.czt.z.ast.Signature state = (net.sourceforge.czt.z.ast.Signature) args[1];
      java.util.List attribute = (java.util.List) args[2];
      java.util.List operation = (java.util.List) args[3];
      zedObject = new ClassSigImpl();
      if (classes != null) {
        zedObject.getClasses().addAll(classes);
      }
      zedObject.setState(state);
      if (attribute != null) {
        zedObject.getAttribute().addAll(attribute);
      }
      if (operation != null) {
        zedObject.getOperation().addAll(operation);
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
    Object[] erg = { getClasses(), getState(), getAttribute(), getOperation() };
    return erg;
  }


  private net.sourceforge.czt.base.ast.ListTerm classes_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(ClassRef.class);

  public net.sourceforge.czt.base.ast.ListTerm getClasses()
  {
    return classes_;
  }

  private net.sourceforge.czt.z.ast.Signature state_;

  public net.sourceforge.czt.z.ast.Signature getState()
  {
    return state_;
  }

  public void setState(net.sourceforge.czt.z.ast.Signature state)
  {
    state_ = state;
  }


  private net.sourceforge.czt.base.ast.ListTerm attribute_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(net.sourceforge.czt.z.ast.NameTypePair.class);

  public net.sourceforge.czt.base.ast.ListTerm getAttribute()
  {
    return attribute_;
  }


  private net.sourceforge.czt.base.ast.ListTerm operation_ =
    new net.sourceforge.czt.base.impl.ListTermImpl(NameSignaturePair.class);

  public net.sourceforge.czt.base.ast.ListTerm getOperation()
  {
    return operation_;
  }
}
