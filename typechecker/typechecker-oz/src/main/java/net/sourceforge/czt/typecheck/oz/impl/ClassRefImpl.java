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

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * An implementation for ClassRef that hides VariableType instances
 * if they have a value.
 */
public class ClassRefImpl
  extends TermImpl
  implements ClassRef
{
  protected ClassRefImpl(ClassRef classRef)
  {
    super(classRef);
  }

  public void setName(ZName name)
  {
    ClassRef classRef = (ClassRef) term_;
    classRef.setName(name);
  }

  public ZName getName()
  {
    ClassRef classRef = (ClassRef) term_;
    ZName result = classRef.getName();
    return result;
  }

  public ListTerm<NewOldPair> getNewOldPair()
  {
    ClassRef classRef = (ClassRef) term_;
    ListTerm<NewOldPair> result = classRef.getNewOldPair();
    return result;
  }

  public ListTerm<Type2> getType()
  {
    ClassRef classRef = (ClassRef) term_;
    ListTerm<Type2> result = classRef.getType();
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

  public ClassRefImpl create(Object [] args)
  {
    ClassRef classRef = (ClassRef) term_.create(args);
    ClassRefImpl result = new ClassRefImpl(classRef);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof ClassRefVisitor) {
      ClassRefVisitor<R> visitor = (ClassRefVisitor<R>) v;
      return visitor.visitClassRef(this);
    }
    return super.accept(v);
  }

  public String toString()
  {
    ClassRef classRef = (ClassRef) term_;
    return classRef.toString();
  }

  public boolean equals(Object obj)
  {

    if (obj != null) {
      if (obj instanceof ClassRef) {
        ClassRef classRef = (ClassRef) obj;
        if (getName() != null) {
          if (!getName().equals(classRef.getName())) {
            return false;
          }
        }
        else {
          if (classRef.getName() != null) {
            return false;
          }
        }

        if (getType().size() == classRef.getType().size()) {
          for (int i = 0; i < getType().size(); i++) {
            Type2 typeA = (Type2) getType().get(i);
            Type2 typeB = (Type2) classRef.getType().get(i);
            if (!typeA.equals(typeB)) {
              return false;
            }
          }
        }
        if (getNewOldPair() != null) {
          if (!getNewOldPair().equals(classRef.getNewOldPair())) {
            return false;
          }
        }

        return true;
      }
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ClassRefImpl".hashCode();
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}
