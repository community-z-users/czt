/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.oz.impl;

import java.util.List;

import net.sourceforge.czt.z.ast.DeclName;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.oz.ast.ClassSig;
import net.sourceforge.czt.oz.visitor.ClassSigVisitor;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * An implementation for ClassSig that represents a class
 * signature variable.
 */
public class VariableClassSig
  extends net.sourceforge.czt.base.impl.TermImpl
  implements ClassSig
{
  /**
   * The Greek psi character as a string. Prefix with an
   * underscore to avoid clashes with user-defined variables.
   */
  //protected static final String PSI = "_" + Character.toString('\u03C8');
  protected static final String PSI = "_PSI";

  /** The number stroke of the next psi variable. */
  protected static int serial_ = 0;

  /** The name of this variable. */
  protected DeclName declName_ = null;

  /** The unified value of this signature. */
  protected ClassSig value_ = null;

  protected VariableClassSig(Factory factory)
  {
    List<Stroke> strokes = new java.util.ArrayList();
    strokes.add(factory.createNumStroke(new Integer(serial_++)));
    declName_ = factory.createDeclName(PSI, strokes, null);
  }

  protected VariableClassSig(DeclName declName)
  {
    declName_ = declName;
  }

  /**
   * @return the value of the unified signature, or this signature if
   * it is not yet unified
   */
  public ClassSig getValue()
  {
    if (value_ == null) {
      return this;
    }
    else {
      if (value_ instanceof VariableClassSig && value_ != this) {
        VariableClassSig vType = (VariableClassSig) value_;
        return vType.getValue();
      }
      return value_;
    }
  }

  /**
   * Set the value of the signature.
   * @param signature the value of the signature
   */
  public void setValue(ClassSig signature)
  {
    value_ = signature;
  }

  /**
   * Get the variable name associated with this type.
   */
  public DeclName getName()
  {
    return declName_;
  }

  /**
   * Set the variable name associated with this type.
   */
  public void setName(DeclName declName)
  {
    declName_ = declName;
  }

  public Object[] getChildren()
  {
    Object[] result = {getClasses(), getState(), getAttribute(), getOperation() };
    return result;
  }

  public void setState(net.sourceforge.czt.z.ast.Signature signature)
  {
  }

  public net.sourceforge.czt.z.ast.Signature getState()
  {
    return null;
  }

  public net.sourceforge.czt.base.ast.ListTerm getAttribute()
  {
    return new net.sourceforge.czt.base.impl.ListTermImpl();
  }

  public net.sourceforge.czt.base.ast.ListTerm getOperation()
  {
    return new net.sourceforge.czt.base.impl.ListTermImpl();
  }

  public net.sourceforge.czt.base.ast.ListTerm getClasses()
  {
    return new net.sourceforge.czt.base.impl.ListTermImpl();
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
    VariableClassSig zedObject = null;
    return zedObject;
  }

  public String toString()
  {
    String result = new String();

    if (value_ != null) {
      result += value_.toString();
    }
    else if (declName_.getWord().indexOf(PSI) >= 0) {
      result += declName_.toString();
    }
    else {
      result += "VCSIG(" + declName_.toString() + ")";
    }

    return result;
  }

  public boolean equals(Object o)
  {
    boolean result = false;

    if (o instanceof VariableClassSig) {
      VariableClassSig variableClassSig =
        (VariableClassSig) o;
      if (declName_.equals(variableClassSig.getName())) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "VariableClassSig".hashCode();
    if (declName_ != null) {
      hashCode += constant * declName_.hashCode();
    }
    return hashCode;
  }
}
