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
import net.sourceforge.czt.z.impl.Type2Impl;
import net.sourceforge.czt.base.impl.ListTermImpl;

/**
 * An UnknownType is used when the type of an expression cannot be
 * determined. If the RefExpr in this type is non-null, then the type
 * is undetermined because the name in the RefExpr is not yet
 * declared.
 */
public class UnknownType
  extends Type2Impl
{
  /** The undefined reference associated with this type. */
  protected ZName zName_;

  /** The list of instantiations associated with this type. */
  protected List<Type2> types_;

  /** The list of renames associated with this type. */
  protected List<NewOldPair> pairs_;

  /** True iff zName_ is the superset of this type. */
  protected boolean isMem_;

  protected UnknownType(ZName zName,
                        boolean isMem,
                        List<Type2> types,
                        List<NewOldPair> pairs)
  {
    zName_ = zName;
    isMem_ = isMem;
    types_ = types;
    pairs_ = pairs;
  }

  protected UnknownType(ZName zName,
                        boolean isMem,
                        List<Type2> types)
  {
    this(zName, isMem, types, new ListTermImpl<NewOldPair>());
  }

  protected UnknownType(ZName zName, boolean isMem)
  {
    this(zName, isMem, new ListTermImpl<Type2>());
  }

  protected UnknownType(ZName zName)
  {
    this(zName, false);
  }

  protected UnknownType()
  {
    this(null);
  }

  public List<Type2> getType()
  {
    List<Type2> result = types_;
    for (int i = 0; i < result.size(); i++) {
      Type2 type = (Type2) result.get(i);
      if (type instanceof VariableType) {
        VariableType vType = (VariableType) type;
        if (vType.getValue() != vType) {
          result.set(i, vType.getValue());
        }
      }
    }
    return result;
  }

  public List<NewOldPair> getPairs()
  {
    return pairs_;
  }

  /**
   * Get the undefined reference associated with this type.
   */
  public ZName getZName()
  {
    return zName_;
  }

  /**
   * Set the undefined reference associated with this type.
   */
  public void setZName(ZName zName)
  {
    zName_ = zName;
  }

  public void setIsMem(boolean isMem)
  {
    isMem_ = isMem;
  }

  public boolean getIsMem()
  {
    return isMem_;
  }

  public boolean equals(Object obj)
  {
    boolean result = false;

    if (obj instanceof UnknownType) {
      UnknownType unknownType = (UnknownType) obj;
      if (zName_ == null && unknownType.getZName() == null) {
        result = true;
      }
      else if (zName_ != null && zName_.equals(unknownType.getZName())) {
        result = true;
      }

      if (result && isMem_ == unknownType.getIsMem()) {
        result = true;
      }
    }

    return result;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "UnknownType".hashCode();
    if (zName_ != null) {
      hashCode += constant * zName_.hashCode();
    }
    return hashCode;

  }

  public Object [] getChildren()
  {
    Object [] children = { getZName(), getType(), Boolean.valueOf(getIsMem()) };
    return children;
  }

  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof UnknownTypeVisitor) {
      UnknownTypeVisitor<R> visitor = (UnknownTypeVisitor<R>) v;
      return visitor.visitUnknownType(this);
    }
    return super.accept(v);
  }

  public UnknownType create(java.lang.Object[] args)
  {
    UnknownType zedObject = null;
    try {
      zedObject = new UnknownType();
      ZName zName = (ZName) args[0];
      @SuppressWarnings("unchecked")
	List<Type2> types = (List<Type2>) args[1];
      Boolean isMem = (Boolean) args[2];
      zedObject.setZName(zName);
      zedObject.setIsMem(isMem);
      zedObject.getType().addAll(types);
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
    StringBuilder result = new StringBuilder("unknown");

    if (zName_ != null) {
      result.append("(");
      if (getIsMem()) {
        result.append("member(");
      }
      result.append(zName_);
      if (getIsMem()) {
    	  result.append(")");
      }
      if (types_.size() > 0) {
    	  result.append("[");
    	  result.append(types_.get(0).toString());
        for (int i = 1; i < types_.size(); i++) {
        	result.append(", ");
        	result.append(types_.get(i).toString());
        }
        result.append("]");
      }
      if (pairs_.size() > 0) {
    	  result.append("[");
    	  result.append(pairs_.get(0).getNewName().toString() + "/");
    	  result.append(pairs_.get(0).getOldName().toString());
        for (int i = 1; i < pairs_.size(); i++) {
        	result.append(", ");
        	result.append(pairs_.get(i).getNewName().toString() + "/");
        	result.append(pairs_.get(i).getOldName().toString());
        }
        result.append("]");
      }
      result.append(")");
    }
    return result.toString();
  }
}
