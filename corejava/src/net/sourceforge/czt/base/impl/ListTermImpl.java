/*
  Copyright (C) 2004, 2005 Mark Utting
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
import java.util.List;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.util.Visitor;

/**
 * <p>A list implementation that integrates nicely into the AST.</p>
 *
 * @author Petra Malik
 */
public class ListTermImpl<E>
  extends AbstractList<E>
  implements List<E>, ListTerm<E>
{
  /**
   * The list containing the data.
   */
  /*@ non_null @*/
  private List<E> list_ = new ArrayList<E>();

  /**
   * Constructs an empty list term that accepts all Objects.
   */
  public ListTermImpl()
  {
    super();
  }

  /**
   * Constructs an empty list term that accepts elements of
   * the specified class.
   *
   * @param aClass ignored
   */
  public ListTermImpl(Class aClass)
  {
    super();
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
  public E set(int index, E element)
  {
    return list_.set(index, element);
  }

  /**
   * Returns the number of components in this list.
   */
  public int size()
  {
    return list_.size();
  }

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

  public Object[] getChildren()
  {
    return list_.toArray();
  }

  public Term create(Object[] args)
  {
    ListTermImpl<E> result = new ListTermImpl<E>();
    for (int i = 0; i < args.length; i++) {
      result.add((E) args[i]);
    }
    return result;
  }
}
