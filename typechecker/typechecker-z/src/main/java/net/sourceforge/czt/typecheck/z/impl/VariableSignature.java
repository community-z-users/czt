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

import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for Signature that represents a signature variable.
 */
public class VariableSignature
  extends net.sourceforge.czt.base.impl.TermImpl
  implements Signature
{
  /**
   * The Greek beta character as a string. Prefix with an
   * underscore to avoid clashes with user-defined variables.
   */
  protected static final String BETA = "_" + Character.toString('\u03B2');

  /** The number stroke of the next beta variable. */
  protected static int serial_ = 0;

  /** The name of this variable. */
  protected ZName zName_ = null;

  /** The unified value of this signature. */
  protected Signature value_ = null;

  protected VariableSignature(Factory factory)
  {
    ZStrokeList strokes = factory.getZFactory().createZStrokeList();
    //    strokes.add(factory.createNumStroke(new Integer(serial_++)));
    zName_ = factory.createZDeclName(BETA, strokes);
  }

  protected VariableSignature(ZName zName)
  {
    zName_ = zName;
  }

  /**
   * @return the value of the unified signature, or this signature if
   * it is not yet unified
   */
  public Signature getValue()
  {
    if (value_ == null) {
      return this;
    }
    else {
      if (value_ instanceof VariableSignature) {
        VariableSignature vType = (VariableSignature) value_;
        return vType.getValue();
      }
      return value_;
    }
  }

  /**
   * Set the value of the signature.
   * @param signature the value of the signature
   */
  public void setValue(Signature signature)
  {
    value_ = signature;
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
    Object[] result = { getName(), value_, getNameTypePair() };
    return result;
  }

  public net.sourceforge.czt.base.ast.ListTerm<NameTypePair> getNameTypePair()
  {
    return new net.sourceforge.czt.base.impl.ListTermImpl<NameTypePair>();
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof VariableSignatureVisitor) {
      VariableSignatureVisitor<R> visitor = (VariableSignatureVisitor<R>) v;
      return visitor.visitVariableSignature(this);
    }
    return super.accept(v);
  }

  /**
   * Returns a new object of this class.
   */
  public VariableSignature create(Object[] args)
  {
    VariableSignature zedObject = null;
    try {
      ZName zName = (ZName) args[0];
      zedObject = new VariableSignature(zName);
      Signature value = (Signature) args[1];
      zedObject.setValue(value);
      @SuppressWarnings("unchecked")
	List<NameTypePair> pairs = (List<NameTypePair>) args[2];
      zedObject.getNameTypePair().addAll(pairs);
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
    else if (zName_.getWord().indexOf(BETA) >= 0) {
      result += zName_.toString();
    }
    else {
      result += "VSIG(" + zName_.toString() + ")";
    }

    return result;
  }

  public boolean equals(Object o)
  {
    boolean result = false;

    if (o instanceof VariableSignature) {
      VariableSignature variableSignature = (VariableSignature) o;
      if (zName_.equals(variableSignature.getName())) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "VariableSignature".hashCode();
    if (zName_ != null) {
      hashCode += constant * zName_.hashCode();
    }
    return hashCode;
  }
}
