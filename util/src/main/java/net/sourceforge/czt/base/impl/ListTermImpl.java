/*
  Copyright (C) 2004, 2005, 2006 Mark Utting
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

import java.util.AbstractList;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.Visitor;

/**
 * <p>A list implementation that integrates nicely into the AST.</p>
 *
 * @param <E> the type of the elements in this list.
 * @author Petra Malik
 */
public class ListTermImpl<E>
  extends AbstractList<E>
  implements ListTerm<E>
{
  /**
   * The list containing the data.
   */
  /*@ non_null @*/
  private final List<E> list_;

  /**
   * A list of annotations.
   */
  private List<Object> anns_;

  private BaseFactory factory_;


  /**
   * Constructs an empty list term that accepts all Objects.
   */
  public ListTermImpl()
  {
    super();
    anns_ = null;
    factory_ = null;
    list_ = new ArrayList<E>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  }

  protected ListTermImpl(BaseFactory factory)
  {
    super();
    factory_ = factory;
    anns_ = null;
    list_ = new ArrayList<E>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  }

  @Override
  public String toString()
  {
    try {
      if (factory_ != null) {
        final String result = factory_.toString(this);
        if (result != null) return result;
      }
    }
    catch (Exception e) {
      e.printStackTrace();
    }
    return super.toString();
  }
  
  /**
   * Inserts the specified element at the specified position in this list.
   * Shifts the element currently at that position (if any) and any
   * subsequent elements to the right (adds one to their indices).
   *
   * @param index the index at which the specified element is to be inserted.
   * @param element the element to be inserted.
   * @throws IndexOutOfBoundsException if the index is out of range
   *         <code>(index < 0 || index > size())</code>.
   */
  @Override
  public void add(int index, E element)
  {
    list_.add(index, element);
  }

  /**
   * Returns the element at the specified position in this list.
   *
   * @param index the index of the elment to be returned.
   * @return the element at the specified position in this list.
   * @throws IndexOutOfBoundsException if the index is out of range
   *         <code>(index < 0 || index >= size())</code>.
   */
  @Override
  public E get(int index)
  {
    return list_.get(index);
  }

  /**
   * Removes the element at the specified position in this list.
   * Shifts any subsequent elements to the left
   * (subtracts one from their indices).
   * Returns the element that was removed from the list.
   *
   * @param index the index of the element to be removed.
   * @return the element previously at the specified position.
   * @throws IndexOutOfBoundsException if the index is out of range
   *         <code>(index < 0 || index >= size())</code>.
   */
  public E remove(int index)
  {
    return list_.remove(index);
  }

  /**
   * Replaces the elment at the specifed position
   * in this list with the specified element.
   *
   * @param index the position of the element to replace.
   * @param element the new element to be stored at the specified position.
   * @return the element previously at the specified position.
   * @throws ArrayIndexOutOfBoundsException if <code>index</code>
   *         is out of range <code>(index < 0 || index >= size())</code>.
   */
  @Override
  public E set(int index, E element)
  {
    return list_.set(index, element);
  }

  /**
   * Returns the number of components in this list.
   * @return
   */
  @Override
  public int size()
  {
    return list_.size();
  }

  @Override
  public <R> R accept(Visitor<R> v)
  {
    if (v instanceof ListTermVisitor) {
      ListTermVisitor<R> visitor = (ListTermVisitor<R>) v;
      return visitor.visitListTerm(this);
    }
    if (v instanceof TermVisitor) {
      TermVisitor<R> visitor = (TermVisitor<R>) v;
      return visitor.visitTerm(this);
    }
    return null;
  }

  @Override
  public Object[] getChildren()
  {
    return list_.isEmpty() ? new Object[0] : list_.toArray();
  }

  @SuppressWarnings("unchecked")
@Override
  public Term create(Object[] args)
  {
    ListTermImpl<E> result = new ListTermImpl<E>();
    for (int i = 0; i < args.length; i++) {
      result.add((E) args[i]);
    }
    return result;
  }

  @Override
  public /*ListTerm<Object>*/ List<Object> getAnns()
  {
    // Why this weird result here? Unique per call? why not just like in Term?
    //ListTermImpl<Object> result = new ListTermImpl<Object>();
    //result.addAll(anns_);
    //return result;

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
    if (hasAnn())
    {
      for (Object annotation : getAnns()) {
        if (aClass.isInstance(annotation)) {
          return (T)annotation;
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
    if (hasAnn())
    {
      List<Object> anns = getAnns();
      for (Iterator<Object> iter = anns.iterator(); iter.hasNext(); )
      {
        Object ann = iter.next();
        if (aClass.isInstance(ann))
        {
          iter.remove();
        }
      }
    }
  }

  @Override
  public <T> boolean removeAnn(T annotation)
  {
    boolean result = false;
    if (hasAnn())
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
    }
    return result;
  }
}
