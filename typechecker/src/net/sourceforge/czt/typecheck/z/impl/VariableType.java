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
package net.sourceforge.czt.typecheck.z.impl;

import java.util.List;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;;

/**
 * A VariableType.
 */
public class VariableType
  extends Type2Impl
{
  /**
   * The Greek alpha character as a string. Prefix with an underscore
   * to avoid clashes with user-defined variables.
   */
  protected static final String ALPHA = "_" + Character.toString('\u03B1');

  /** The number stroke of the next alpha variable. */
  protected static int serial_ = 0;

  /** The name of this variable. */
  protected ZDeclName zDeclName_ = null;

  /** The value of this variable. */
  protected Type2 value_ = null;

  protected VariableType(Factory factory)
  {
    super(null);
    List<Stroke> strokes = factory.list();
    strokes.add(factory.createNumStroke(new Integer(serial_++)));
    zDeclName_ = factory.createZDeclName(ALPHA, strokes, null);
  }

  protected VariableType(ZDeclName zDeclName)
  {
    super(null);
    zDeclName_ = zDeclName;
  }

  /**
   * @return The value of this variable, or itself if no value as been
   * assigned.
   */
  public Type2 getValue()
  {
    if (value_ == null) {
      return this;
    }
    else {
      if (value_ instanceof VariableType) {
        VariableType vType = (VariableType) value_;
        return vType.getValue();
      }
      return value_;
    }
  }

  /**
   * Sets the value of this variable.
   * @param value - the value of this variable.
   */
  public void setValue(Type2 value)
  {
    if (value_ instanceof VariableType) {
      VariableType vType = (VariableType) value_;
      vType.setValue(value);
    }
    else {
      value_ = value;
    }
  }

  /**
   * Get the variable name associated with this type.
   */
  public ZDeclName getName()
  {
    return zDeclName_;
  }

  /**
   * Set the variable name associated with this type.
   */
  public void setName(ZDeclName zDeclName)
  {
    zDeclName_ = zDeclName;
  }

  public Object[] getChildren()
  {
    Object [] result = { getName(), value_ };
    return result;
  }

  public VariableType create(Object[] args)
  {
    VariableType zedObject = null;
    try {
      ZDeclName zDeclName = (ZDeclName) args[0];
      Type2 value = (Type2) args[1];
      zedObject = new VariableType(zDeclName);
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

  public String toString()
  {
    String result = new String();

    if (value_ != null) {
      result += value_.toString();
    }
    else if (zDeclName_.getWord().indexOf(ALPHA) >= 0) {
      result += zDeclName_.toString();
    }
    else {
      result += "VTYPE(" + zDeclName_.toString() + ")";
    }

    return result;
  }

  public boolean equals(Object o)
  {
    boolean result = false;

    if (o instanceof VariableType) {
      VariableType variableType = (VariableType) o;
      if (zDeclName_.equals(variableType.getName())) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = 0;
    hashCode += "VariableType".hashCode();
    if (zDeclName_ != null) {
      hashCode += constant * zDeclName_.hashCode();
    }
    return hashCode;
  }

  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof VariableTypeVisitor) {
      VariableTypeVisitor<R> visitor = (VariableTypeVisitor<R>) v;
      return visitor.visitVariableType(this);
    }
    return super.accept(v);
  }
}
