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

import net.sourceforge.czt.base.ast.Term;
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
  /** The class signature of this class type. */
  protected ClassSig classSig_ = null;

  /** The possible types of this variable. */
  protected List<ClassType> types_ = new java.util.ArrayList<ClassType>();

  /** If this type is completely determined. */
  protected boolean complete_ = false;

  protected VariableClassType(Factory factory)
  {
    super(factory);
    classSig_ = factory.createVariableClassSig();
  }

  protected VariableClassType(DeclName declName)
  {
    super(declName);
  }

  /**
   * Returns the ClassSig element.
   *
   * @return the ClassSig element.
   */
  public ClassSig getClassSig()
  {
    ClassSig result = classSig_;
    Type2 type = getValue();
    if (type instanceof ClassType && type != this) {
      ClassType classType = (ClassType) type;
      result = classType.getClassSig();
    }
    return result;
  }

  /**
   * Sets the ClassSig element.
   *
   * @param classSig   the ClassSig element.
   * @see #getClassSig
   */
  public void setClassSig(ClassSig classSig)
  {
    throw new RuntimeException("Cannot set signature of VariableClassType");
  }

  /**
   * @return The types of this variable.
   */
  public List<ClassType> getTypes()
  {
    return types_;
  }

  /**
   * Sets the possible types of the type.
   */
  public void setTypes(List<ClassType> types)
  {
    types_ = types;
  }

  public boolean getComplete()
  {
    return complete_;
  }

  public void complete()
  {
    complete_ = true;
  }

  public Type2 getValue()
  {
    Type2 result = super.getValue();
    if (complete_ && types_.size() == 1) {
      value_ = types_.get(0);
      assert value_ != null;
      return value_;
    }
    return result;
  }

  public Object[] getChildren()
  {
    Object[] result = { getName(), value_, getTypes() };
    return result;
  }

  public Term create(Object[] args)
  {
    VariableClassType zedObject = null;
    try {
      DeclName declName = (DeclName) args[0];
      List<ClassType> types = (List<ClassType>) args[1];
      Type2 value = (Type2) args[2];
      zedObject = new VariableClassType(declName);
      zedObject.setValue(value);
      zedObject.setTypes(types);
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
