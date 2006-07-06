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
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * An implementation for ClassRefType that hides VariableClassSig
 * instances if they have a value.
 */
public class ClassRefTypeImpl
  extends ClassTypeImpl
  implements ClassRefType
{
  protected ClassRefTypeImpl(ClassRefType classRefType)
  {
    super(classRefType);
  }

  public void setThisClass(ClassRef classRef)
  {
    ClassRefType classRefType = (ClassRefType) term_;
    classRefType.setThisClass(classRef);
  }

  public ClassRef getThisClass()
  {
    ClassRefType classRefType = (ClassRefType) term_;
    ClassRef result = classRefType.getThisClass();
    return result;
  }

  public ListTerm<ClassRef> getSuperClass()
  {
    ClassRefType classRefType = (ClassRefType) term_;
    ListTerm<ClassRef> result = classRefType.getSuperClass();
    return result;
  }

  public ListTerm<DeclName> getPrimary()
  {
    ClassRefType classRefType = (ClassRefType) term_;
    ListTerm<DeclName> result = classRefType.getPrimary();
    return result;
  }

  public void setVisibilityList(VisibilityList visibilityList)
  {
    ClassRefType classRefType = (ClassRefType) term_;
    classRefType.setVisibilityList(visibilityList);
  }

  public VisibilityList getVisibilityList()
  {
    ClassRefType classRefType = (ClassRefType) term_;
    VisibilityList result = classRefType.getVisibilityList();
    return result;
  }

  public ClassRefTypeImpl create(Object [] args)
  {
    ClassRefType classRefType = (ClassRefType) term_.create(args);
    ClassRefTypeImpl result = new ClassRefTypeImpl(classRefType);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof ClassRefTypeVisitor) {
      ClassRefTypeVisitor<R> visitor = (ClassRefTypeVisitor<R>) v;
      return visitor.visitClassRefType(this);
    }
    return super.accept(v);
  }
}
