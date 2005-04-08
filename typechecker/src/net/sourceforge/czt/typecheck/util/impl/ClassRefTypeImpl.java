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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.oz.ast.*;

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

  public ListTerm getSuperClass()
  {
    ClassRefType classRefType = (ClassRefType) term_;
    ListTerm result = classRefType.getSuperClass();
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

  public net.sourceforge.czt.base.ast.Term create(Object [] args)
  {
    ClassRefType classRefType = (ClassRefType) term_.create(args);
    ClassRefType result = new ClassRefTypeImpl(classRefType);
    return result;
  }
}
