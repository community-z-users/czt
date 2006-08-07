/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.rules.ast;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.impl.DeclListImpl;

/**
 * An empty decl list
 *
 * @author Petra Malik
 */
public class EmptyDeclListImpl
  extends DeclListImpl
  implements EmptyDeclList
{
  public EmptyDeclListImpl()
  {
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof EmptyDeclListVisitor) {
      EmptyDeclListVisitor<R> edlv = (EmptyDeclListVisitor<R>) visitor;
      return edlv.visitEmptyDeclList(this);
    }
    else {
      return super.accept(visitor);
    }
  }

  public EmptyDeclListImpl create(Object[] args)
  {
    return new EmptyDeclListImpl();
  }

  public Object[] getChildren()
  {
    return new Object[] {};
  }
}
