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

public class TypesafeList
  extends AbstractList
{
  private List list_ = new Vector();
  private Class class_ = null;

  public TypesafeList(Class aClass)
  {
    class_ = aClass;
  }

  public void add(int index, Object element)
  {
    if (! class_.isInstance(element)) {
      String message = element.getClass().getName()
        + " cannot be inserted into a list of "
        + class_.getName();
                                   
      throw new ClassCastException(message);
    }
    list_.add(index, element);
  }

  public Object get(int index)
  {
    return list_.get(index);
  }

  public Object remove(int index)
  {
    return list_.remove(index);
  }

  public Object set(int index, Object element)
  {
    if (! class_.isInstance(element)) {
      throw new ClassCastException();
    }
    return list_.set(index, element);
  }

  public int size()
  {
    return list_.size();
  }
}
