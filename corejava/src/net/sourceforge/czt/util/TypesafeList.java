/**
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.util;

import java.util.AbstractList;
import java.util.List;
import java.util.Vector;

/**
 * A typesafe list implementation.
 *
 * @author Petra Malik
 */
public class TypesafeList
  extends AbstractList
{
  /**
   * The list containing the data.
   */
  private List list_ = new Vector();

  /**
   * All elements in this list should be an instance
   * of this class.
   */
  private Class class_ = null;

  /**
   * Constructs an empty list that accepts elements of
   * the specified class.
   *
   * @param aClass the class for which instances will be accepted
   *               by this list.
   */
  public TypesafeList(Class aClass)
  {
    class_ = aClass;
  }

  /**
   * Inserts the specified element at the specified position in this list.
   * Shifts the element currently at that position (if any) and any
   * subsequent elements to the right (adds one to their indices).
   *
   * @param index the index at which the specified element is to be inserted.
   * @param element the element to be inserted.
   * @throws ClassCastException if the class of the specified element
   *         prevents it from being added to this list.
   * @throws IndexOutOfBoundsException if the index is out of range
   *         <code>(index < 0 || index > size())</code>.
   */
  public void add(int index, Object element)
  {
    if (!class_.isInstance(element)) {
      String message = element.getClass().getName()
        + " cannot be inserted into a list of "
        + class_.getName();
      throw new ClassCastException(message);
    }
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
  public Object get(int index)
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
  public Object remove(int index)
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
   * @throws ClassCastException if the object is not accepted by this list.
   */
  public Object set(int index, Object element)
  {
    if (!class_.isInstance(element)) {
      throw new ClassCastException();
    }
    return list_.set(index, element);
  }

  /**
   * Returns the number of components in this list.
   */
  public int size()
  {
    return list_.size();
  }
}
