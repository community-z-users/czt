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
  static int serial_ = 0;

  /** The name of this variable. */
  protected ZName zName_ = null;

  /** The value of this variable. */
  protected Type2 value_ = null;
  
  private static synchronized void incrementSerial()
  {
	  serial_++;
  }

  protected VariableType(Factory factory)
  {
    super(null);
    ZStrokeList strokes = factory.getZFactory().createZStrokeList();
    String strokeString = Integer.toString(serial_);
    incrementSerial();
    for (int i = 0; i < strokeString.length(); i++) {
      Integer iStroke = Integer.parseInt(strokeString.substring(i, i + 1));
      strokes.add(factory.createNumStroke(iStroke));
    }
    zName_ = factory.createZDeclName(ALPHA, strokes);
  }

  protected VariableType(ZName zName)
  {
    super(null);
    zName_ = zName;
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
  public ZName getName()
  {
    return zName_;
  }

  /**
   * Set the variable name associated with this type.
   */
  public void setName(ZName zName)
  {
    zName_ = zName;
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
      ZName zName = (ZName) args[0];
      Type2 value = (Type2) args[1];
      zedObject = new VariableType(zName);
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
    String result = "";

    if (value_ != null) {
      result += value_.toString();
    }
    else if (zName_.getWord().indexOf(ALPHA) >= 0) {
      result += zName_.toString();
    }
    else {
      result += "VTYPE(" + zName_.toString() + ")";
    }

    return result;
  }

  public boolean equals(Object o)
  {
    boolean result = false;

    if (o instanceof VariableType) {
      VariableType variableType = (VariableType) o;
      if (zName_.equals(variableType.getName())) {
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
    if (zName_ != null) {
      hashCode += constant * zName_.hashCode();
    }
    return hashCode;
  }

  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof VariableTypeVisitor) {
      VariableTypeVisitor<R> visitor = (VariableTypeVisitor<R>) v;
      return visitor.visitVariableType(this);
    }
    if (getValue() != this) {
      return getValue().accept(v);
    }
    return super.accept(v);
    //throw new IllegalArgumentException();
  }
}
