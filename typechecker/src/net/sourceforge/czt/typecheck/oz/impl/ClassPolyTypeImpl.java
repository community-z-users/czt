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
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * An implementation for ClassPolyType that hides VariableClassSig
 * instances if they have a value.
 */
public class ClassPolyTypeImpl
  extends ClassTypeImpl
  implements ClassPolyType
{
  protected ClassPolyTypeImpl(ClassPolyType classPolyType)
  {
    super(classPolyType);
  }

  public void setRootClass(ClassRef classRef)
  {
    ClassPolyType classPolyType = (ClassPolyType) term_;
    classPolyType.setRootClass(classRef);
  }

  public ClassRef getRootClass()
  {
    ClassPolyType classPolyType = (ClassPolyType) term_;
    ClassRef result = classPolyType.getRootClass();
    return result;
  }

  public net.sourceforge.czt.base.ast.Term create(Object [] args)
  {
    ClassPolyType classPolyType = (ClassPolyType) term_.create(args);
    ClassPolyType result = new ClassPolyTypeImpl(classPolyType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public Object accept(net.sourceforge.czt.util.Visitor v)
  {
    if (v instanceof ClassPolyTypeVisitor) {
      ClassPolyTypeVisitor visitor = (ClassPolyTypeVisitor) v;
      return visitor.visitClassPolyType(this);
    }
    return super.accept(v);
  }
}
