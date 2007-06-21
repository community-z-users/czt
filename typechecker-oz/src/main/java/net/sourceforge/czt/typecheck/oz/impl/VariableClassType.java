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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A Variable ClassType.
 */
public class VariableClassType
  extends VariableType
  implements ClassType
{
  /** The candidate type of this variable. */
  protected ClassType candidateType_ = null;

  protected VariableClassType(Factory factory)
  {
    super(factory);
  }

  protected VariableClassType(ZName zName)
  {
    super(zName);
  }

  public ClassRefList getClasses()
  {
    ClassRefList result = null;
    if (getClassValue() != null) {
      result = getClassValue().getClasses();
    }
    return result;
  }

  public void setClasses(ClassRefList classRefList)
  {
    assert false : "Cannot set ClassRefList of VariableClassType";
  }

  public Signature getState()
  {
    Signature result = null;
    if (getClassValue() != null) {
      result = getClassValue().getState();
    }
    return result;
  }

  public void setState(Signature state)
  {
    assert false : "Cannot set state of VariableClassType";
  }

  public ListTerm<NameTypePair> getAttribute()
  {
    ListTerm<NameTypePair> result = new ListTermImpl<NameTypePair>();
    if (getClassValue() != null) {
      result = getClassValue().getAttribute();
    }
    return result;
  }

  public ListTerm<NameSignaturePair> getOperation()
  {
    ListTerm<NameSignaturePair> result = new ListTermImpl<NameSignaturePair>();
    if (getClassValue() != null) {
      result = getClassValue().getOperation();
    }
    return result;
  }

  /**
   * Returns the value or the candidate type.
   *
   * @return the value or the candidate type.
   */
  public ClassType getClassValue()
  {
    ClassType result = null;
    if (value_ instanceof ClassType && value_ != this) {
      result = (ClassType) value_;
    }
    else if (candidateType_ != null) {
      result = candidateType_;
    }
    return result;
  }

  /**
   * Set the candidate type of this variable.
   * @param classType the candidiate type.
   */
  public void setCandidateType(ClassType classType)
  {
    candidateType_ = classType;
  }

  /**
   * @return The candidate type of this variable.
   */
  public ClassType getCandidateType()
  {
    if (candidateType_ instanceof VariableClassType) {
      VariableClassType vClassType = (VariableClassType) candidateType_;
      candidateType_ = vClassType.getCandidateType();
    }
    return candidateType_;
  }

  public Object[] getChildren()
  {
    Object[] result = { getName(), value_, getCandidateType()};
    return result;
  }

  public VariableClassType create(Object[] args)
  {
    assert false : "VariableClassType.create called";
    VariableClassType zedObject = null;
    try {
      ZName zName = (ZName) args[0];
      ClassType type = (ClassType) args[1];
      Type2 value = (Type2) args[2];
      zedObject = new VariableClassType(zName);
      zedObject.setValue(value);
      zedObject.setCandidateType(type);
    }
    catch (IndexOutOfBoundsException e) {
      throw new IllegalArgumentException();
    }
    catch (ClassCastException e) {
      throw new IllegalArgumentException();
    }
    return zedObject;
  }

  public boolean equals(Object o)
  {
    boolean result = false;

    if (o instanceof VariableClassType) {
      VariableClassType variableClassType = (VariableClassType) o;
      if (value_.equals(variableClassType.getValue())) {
        result = true;
      }
    }

    return result;
  }

  public String toString()
  {
    String result = "VClassType " + super.toString();
    if (candidateType_ != null) {
      result += " (" + candidateType_ + ")";
    }
    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "VariableClassType".hashCode();
    if (value_ != null) {
      hashCode += constant * value_.hashCode();
    }
    return hashCode;
  }

  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof VariableClassTypeVisitor) {
      VariableClassTypeVisitor<R> visitor = (VariableClassTypeVisitor<R>) v;
      return visitor.visitVariableClassType(this);
    }
    return super.accept(v);
  }
}
