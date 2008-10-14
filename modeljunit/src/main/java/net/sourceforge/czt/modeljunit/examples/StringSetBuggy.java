/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit.examples;

import java.util.AbstractSet;
import java.util.Iterator;
import java.util.Set;
import java.util.ArrayList;

/** A simple implementation of a set of strings.
 *  It does not allow null strings in the set.
 *
 *  The purpose of this class is just to be an example implementation
 *  of Set<String>, which we can run tests on, insert errors into,
 *  measure the coverage of the tests etc.
 *
 *  This class has an intentional bug: the equals method contains an
 *  off-by-one error.
 *
 * @author marku  April 2007 for COMP551
 *
 */
public class StringSetBuggy extends AbstractSet<String>
{
  private ArrayList<String> contents = new ArrayList<String>();

  @Override
  public Iterator<String> iterator()
  {
    return contents.iterator();
  }

  @Override
  public int size()
  {
    return contents.size();
  }

  @Override
  public boolean equals(Object arg0)
  {
    boolean same = false;
    if (arg0 instanceof Set) {
      Set<String> other = (Set<String>) arg0;
      same = size() == other.size();
      // NOTE: this loop is intended to have a bug: i>0 should be i>=0.
      for (int i = contents.size() - 1; same && i > 0; i--) {
        if (!other.contains(contents.get(i)))
          same = false;
      }
    }
    return same;
  }

  @Override
  public void clear()
  {
    contents.clear();
  }

  @Override
  public boolean contains(Object arg0)
  {
    for (int i = contents.size() - 1; i >= 0; i--) {
      if (contents.get(i).equals(arg0))
        return true; // return immediately
    }
    return false; // none match
  }

  @Override
  public boolean isEmpty()
  {
    return contents.size() == 0;
  }

  @Override
  public boolean add(String e)
  {
    if (e == null) {
      throw new NullPointerException();
    }
    if (contents.contains(e)) {
      return false;
    }
    else {
      return contents.add(e); // always adds to end
    }
  }

  @Override
  public boolean remove(Object o)
  {
    if (contents.isEmpty())
      return false;
    else
      return contents.remove(o);
  }
}
