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
package net.sourceforge.czt.typecheck.z.impl;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.*;

/**
 * An implementation for Term that hides VariableType instances
 * if they have a value.
 */
public abstract class TermImpl
  implements Term
{
  /** The Term that this type wraps. */
  protected Term term_;

  protected TermImpl(Term term)
  {
    term_ = term;
  }

  public boolean equals(Object obj)
  {
    return term_.equals(obj);
  }

  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof TermVisitor) {
      TermVisitor<R> visitor = (TermVisitor<R>) v;
      return visitor.visitTerm(this);
    }
    return null;
  }

  public Object [] getChildren()
  {
    return term_.getChildren();
  }

  public int hashCode()
  {
    String s = "Term";
    return s.hashCode();
  }

  public List<Object> getAnns()
  {
    return term_ != null ? term_.getAnns() : null;
  }

  public <T> T getAnn(Class<T> aClass)
  {
    return term_ != null ? term_.getAnn(aClass) : null;
  }
  
  public String toString()
  {
    return term_.toString();
  }
}
