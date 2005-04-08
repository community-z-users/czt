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
package net.sourceforge.czt.typecheck.util.impl;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.oz.ast.*;

/**
 * A Variable ClassType.
 */
public class VariableClassType
  extends Type2Impl
  implements ClassType
{
  /** The values of this variable. */
  protected List<ClassType> value_ = new java.util.ArrayList<ClassType>();

  protected VariableClassType()
  {
    super(null);
  }

  /**
   * Returns the ClassSig element.
   *
   * @return the ClassSig element.
   */
  public ClassSig getClassSig()
  {
    return null;
  }

  /**
   * Sets the ClassSig element.
   *
   * @param classSig   the ClassSig element.
   * @see #getClassSig
   */
  public void setClassSig(ClassSig classSig)
  {
    throw new RuntimeException("Class signautre not permitted in variable class type");
  }

  /**
   * @return The value of this variable.
   */
  public List<ClassType> getValue()
  {
    return value_;
  }

  /**
   * Sets the possible values of the type to the specified value.
   */
  public void setValue(List<ClassType> value)
  {
    value_ = value;
  }

  public Object[] getChildren()
  {
    Object[] result = { getValue() };
    return result;
  }

  public Term create(Object[] args)
  {
    VariableClassType zedObject = null;
    try {
      List<ClassType> value = (List<ClassType>) args[0];
      zedObject = new VariableClassType();
      zedObject.setValue(value);
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

  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof VariableClassTypeVisitor) {
      VariableClassTypeVisitor visitor = (VariableClassTypeVisitor) v;
      return visitor.visitVariableClassType(this);
    }
    return super.accept(v);
  }
}
