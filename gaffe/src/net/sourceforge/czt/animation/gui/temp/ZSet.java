/*
  GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
  Copyright 2003 Nicholas Daley

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.gui.temp;

import java.util.Iterator;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

/**
 * Values in Z that are Sets.
 */
public class ZSet implements ZValue
{
  private final Vector set_;
  /**
   * Construct an empty <code>ZSet</code>.
   */
  public ZSet()
  {
    set_ = new Vector();
  };
  /**
   * Construct a <code>ZSet</code> from a <code>Set</code> of values.
   * @param set The set to store.
   */
  public ZSet(Set/*<ZValue>*/ set)
  {
    set_ = new Vector(set);
  };

  /**
   * @return An iterator over this <code>ZSet</code>.
   */
  public Iterator iterator()
  {
    return set_.iterator();
  };
  /**
   * @return The set's size.
   */
  public int size()
  {
    return set_.size();
  };
  /**
   * @param value A value to look for in this <code>ZSet</code>.
   * @return <code>true</code> if the <code>ZSet</code> contains
   *         <code>value</code>.
   */
  public boolean contains(ZValue value)
  {
    return set_.contains(value);
  };
  /**
   * @param index An index into the set.
   * @return The <code>index</code>th value in the set.
   */
  public ZValue get(int index)
  {
    return (ZValue) set_.get(index);
  };
  /**
   * @return This <code>ZSet</code> translated into a <code>Set</code>.
   */
  public Set getSet()
  {
    return new HashSet(set_);
  };

  /**
   * @return A string representation of this set.
   */
  public String toString()
  {
    String result = "ZSet: { ";
    Iterator it = iterator();
    if (it.hasNext()) result += it.next();
    while (it.hasNext()) result += " , " + it.next();
    result += " }";
    return result;
  };

  /**
   * Compare for equality against another object.
   * @param obj The object to compare against.
   * @return <code>true</code> if <code>obj</code> is a <code>ZSet</code>
   *         containing all of the same values as this one.
   */
  public boolean equals(Object obj)
  {
    return obj instanceof ZSet && ((ZSet) obj).set_.equals(set_);
  };
  /**
   * @return This object's hashcode.
   */
  public int hashCode()
  {
    return set_.hashCode();
  };
};
