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
import java.util.Iterator;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;
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
  private List<Object> anns_;

  protected TermImpl()
  {
    this(null);
  }

  protected TermImpl(BaseFactory factory)
  {
    factory_ = factory;
    anns_ = null;
  }

  public BaseFactory getFactory()
  {
    return factory_;
  }

  @Override
  public <R> R accept(Visitor<R> v)
  {
    if (v instanceof TermVisitor) {
      TermVisitor<R> visitor = (TermVisitor<R>) v;
      return visitor.visitTerm(this);
    }
    return null;
  }

  @Override
  public boolean equals(Object obj)
  {
    if (obj != null && this.getClass().equals(obj.getClass())) {
      return true;
    }
    return false;
  }

  @Override
  public int hashCode()
  {
    String s = "Term";
    return s.hashCode();
  }

  @Override
  public List<Object> getAnns()
  {
    // synchronise the creation bit to avoid races - rare cases? TODO-CHECK
    //synchronized(this)
    //{
      if (anns_ == null) anns_ = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    //}
    assert anns_ != null;
    return anns_;
  }

  @Override
  public int annsSize()
  {
    return anns_ == null ? 0 : anns_.size();
  }

  @Override
  public boolean hasAnn()
  {
    return annsSize() > 0;
  }

  @Override
  @SuppressWarnings("unchecked")
  public <T> T getAnn(Class<T> aClass)
  {
    if (annsSize() > 0)
    {
      for (Object annotation : getAnns()) {
        if (aClass.isInstance(annotation)) {
          return (T) annotation;
        }
      }
    }
    return null;
  }

  @Override
  public <T> boolean hasAnn(Class<T> aClass)
  {
    return getAnn(aClass) != null;
  }

  @Override
  public <T> void removeAnn(Class<T> aClass)
  {
    if (annsSize() > 0)
    {
      List<Object> anns = getAnns();
      Iterator<Object> iter = anns.iterator();
      while (iter.hasNext())
      {
        Object ann = iter.next();
        if (aClass.isInstance(ann))
        {
          iter.remove();
        }
      }
      iter = null;
    }
  }

  @Override
  public <T> boolean removeAnn(T annotation)
  {
    boolean result = false;
    if (annsSize() > 0)
    {
      List<Object> anns = getAnns();
      Iterator<Object> iter = anns.iterator();
      while (iter.hasNext() && !result)
      {
        Object ann = iter.next();
        result = ann.equals(annotation);
      }
      if (result)
      {
        iter.remove();
      }
      iter = null;
    }
    return result;
  }

  @Override
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
