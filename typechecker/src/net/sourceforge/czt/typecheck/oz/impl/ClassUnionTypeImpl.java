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
 * An implementation for ClassUnionType that hides VariableClassSig
 * instances if they have a value.
 */
public class ClassUnionTypeImpl
  extends ClassTypeImpl
  implements ClassUnionType
{
  protected ClassUnionTypeImpl(ClassUnionType classUnionType)
  {
    super(classUnionType);
  }

  public net.sourceforge.czt.base.ast.Term create(Object [] args)
  {
    ClassUnionType classUnionType = (ClassUnionType) term_.create(args);
    ClassUnionType result = new ClassUnionTypeImpl(classUnionType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof ClassUnionTypeVisitor) {
      ClassUnionTypeVisitor<R> visitor = (ClassUnionTypeVisitor<R>) v;
      return visitor.visitClassUnionType(this);
    }
    return super.accept(v);
  }
}
