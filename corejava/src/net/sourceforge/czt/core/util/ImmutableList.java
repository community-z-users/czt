/*
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

package net.sourceforge.czt.core.util;

import java.util.List;
import java.util.AbstractList;

/**
 * <p>An immutable list.</p>
 *
 * <p>This is a quick implementation of an immutable list.
 * All methods that try to modify this list throw an
 * <code>UnsupportedOperationException</code>.
 *
 * @author Petra Malik
 */
public class ImmutableList extends AbstractList implements List
{
  /**
   * The elements of this list, in correct order.
   */
  private List mList;

  /**
   * Constructs an immutable list containing the elements of the
   * specified list, in the order provided by the given list.
   *
   * @param list the list whose elements are to be placed
   *             into this list.
   * @throws NullPointerException if the given list is null.
   */
  public ImmutableList(List list)
  {
    if (list == null) {
      throw new NullPointerException();
    }
    mList = list;
  }

  public Object get(int index) {
    return mList.get(index);
  }

  public int size()
  {
    return mList.size();
  }
}
