/*
Copyright (C) 2004 Mark Utting
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

package net.sourceforge.czt.base.impl;

import java.util.Iterator;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.util.Visitor;

public class ListTermImpl
  extends TypesafeList
  implements ListTerm
{
  /**
   * Constructs an empty list term that accepts elements of
   * the specified class.
   *
   * @param aClass the class for which instances will be accepted
   *               by this list.
   */
  public ListTermImpl(Class aClass)
  {
    super(aClass);
  }

  public Object accept(Visitor v)
  {
    if (v instanceof ListTermVisitor) {
      ListTermVisitor visitor = (ListTermVisitor) v;
      return visitor.visitListTerm(this);
    }
    if (v instanceof TermVisitor) {
      TermVisitor visitor = (TermVisitor) v;
      return visitor.visitTerm(this);
    }
    return null;
  }

  public Object[] getChildren()
  {
    return toArray();
  }

  public Term create(Object[] args)
  {
    ListTermImpl result = new ListTermImpl(getType());
    for (int i = 0; i < args.length; i++) {
      result.add(args[i]);
    }
    return result;
  }
}
