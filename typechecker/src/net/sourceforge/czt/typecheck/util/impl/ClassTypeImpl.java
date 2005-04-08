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

import net.sourceforge.czt.oz.ast.*;

/**
 * An implementation for ClassRefType that hides VariableClassSig
 * instances if they have a value.
 */
public abstract class ClassTypeImpl
  extends Type2Impl
  implements ClassType
{
  protected ClassTypeImpl(ClassType classType)
  {
    super(classType);
  }

  public void setClassSig(ClassSig classSig)
  {
    ClassType classType = (ClassType) term_;
    classType.setClassSig(classSig);
  }

  public ClassSig getClassSig()
  {
    ClassType classType = (ClassType) term_;
    ClassSig result = classType.getClassSig();
    if (result instanceof VariableClassSig) {
      VariableClassSig vSig = (VariableClassSig) result;
      if (vSig.getValue() != null) {
        result = vSig.getValue();
      }
    }
    return result;
  }

  public String toString()
  {
    ClassType classType = (ClassType) term_;
    return classType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof ClassType) {
      ClassType classType = (ClassType) obj;
      return getClassSig().equals(classType.getClassSig());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "ClassTypeImpl".hashCode();
    if (getClassSig() != null) {
      hashCode += constant * getClassSig().hashCode();
    }
    return hashCode;
  }
}
