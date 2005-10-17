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

package net.sourceforge.czt.rules.unification;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;

/**
 * A wrapper for a HeadDeclList.
 *
 * @author Petra Malik
 */
class HeadDeclListWrapper
  implements Wrapper
{
  private HeadDeclList headDeclList_;
  private String name_;

  public HeadDeclListWrapper(HeadDeclList headDeclList, String name)
  {
    Object[] children = headDeclList.getChildren();
    Term term = (Term) children[0];
    children[0] = term.create(term.getChildren());
    headDeclList_ =
      (HeadDeclList) headDeclList.create(children);
    name_ = name;
  }

  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof TermVisitor) {
      TermVisitor<R> visitor = (TermVisitor<R>) v;
      return visitor.visitTerm(this);
    }
    return null;
  }

  public Term getContent()
  {
    return headDeclList_;
  }

  public Object[] getChildren()
  {
    final List<Decl> list = headDeclList_.getZDeclList();
    if (list.isEmpty()) {
      // should not happen except for printing log messages
      return new Object[] { name_, "?" };
    }
    Decl decl = list.remove(0);
    if (list.isEmpty()) {
      return new Object[] { name_, decl, headDeclList_.getJokerDeclList() };
    }      
    return new Object[] { name_, decl, this };
  }

  public Term create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }
}
