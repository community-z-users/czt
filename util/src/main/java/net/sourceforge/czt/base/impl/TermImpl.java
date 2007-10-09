/*
  Copyright 2003, 2006 Mark Utting
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

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.Visitor;

/**
 * An abstract implementation of the interface {@link Term}.
 *
 * @author Petra Malik
 */
public abstract class TermImpl implements Term
{
  /**
   * The factory that created this Term.
   */
  private BaseFactory factory_;

  /**
   * A list of annotations.
   */
  private List<Object> anns_ = new ArrayList<Object>();

  protected TermImpl()
  {
    factory_ = null;
  }

  protected TermImpl(BaseFactory factory)
  {
    factory_ = factory;
  }

  public BaseFactory getFactory()
  {
    return factory_;
  }

  public <R> R accept(Visitor<R> v)
  {
    if (v instanceof TermVisitor) {
      TermVisitor<R> visitor = (TermVisitor<R>) v;
      return visitor.visitTerm(this);
    }
    return null;
  }

  public boolean equals(Object obj)
  {
    if (obj != null && this.getClass().equals(obj.getClass())) {
      return true;
    }
    return false;
  }
  public int hashCode()
  {
    String s = "Term";
    return s.hashCode();
  }

  public List<Object> getAnns()
  {
    return anns_;
  }

  public <T> T getAnn(Class<T> aClass)
  {
    for (Object annotation : anns_) {
      if (aClass.isInstance(annotation)) {
        return (T) annotation;
      }
    }
    return null;
  }

  public String toString()
  {
    try {
      if (getFactory() != null) {
        final String result = getFactory().toString(this);
        if (result != null) return result;
      }
    }
    catch (Exception e) {
      e.printStackTrace();
    }
    return super.toString();
  }
}
