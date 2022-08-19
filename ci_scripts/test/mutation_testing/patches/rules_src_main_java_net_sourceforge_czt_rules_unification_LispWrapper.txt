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
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.base.visitor.TermVisitor;

class LispWrapper
  implements Wrapper
{
  /** list_ is of type Term! */
  private List<?> list_;
  private String name_;

  /**
   * A list of annotations.
   */
  private ListTerm<Object> anns_ = new ListTermImpl<Object>();

  /**
   * Throws ClassCastException if list is not an instance of Term.
   */
  public LispWrapper(List<?> list, String name)
  {
    Term term = (Term) list;
    list_ = (List<?>) term.create(term.getChildren());
    name_ = name;
  }

  public Term getContent()
  {
    return (Term) list_;
  }

  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof TermVisitor) {
      TermVisitor<R> visitor = (TermVisitor<R>) v;
      return visitor.visitTerm(this);
    }
    return null;
  }

  public Object[] getChildren()
  {
    if (list_.isEmpty()) {
      return new Object[] { name_, null, null };
    }
    return new Object[] { name_, list_.remove(0), this };
  }

  public Term create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }

  public ListTerm<Object> getAnns()
  {
    return anns_;
  }

  @SuppressWarnings("unchecked")
public <T> T getAnn(Class<T> aClass)
  {
    for (Object annotation : anns_) {
      if (aClass.isInstance(annotation)) {
        return (T)annotation;
      }
    }
    return null;
  }

  @Override
  public <T> boolean hasAnn(Class<T> aClass)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public <T> boolean removeAnn(T annotation)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public <T> void removeAnn(Class<T> aClass)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public int annsSize()
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public boolean hasAnn()
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }
}
