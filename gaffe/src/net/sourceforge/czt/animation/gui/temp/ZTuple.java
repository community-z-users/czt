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
import java.util.List;
import java.util.Vector;

/**
 * Class representing Z values that are Tuples.
 */
public class ZTuple implements ZValue
{
  private Vector tuple_;
  /**
   * Construct an empty tuple.
   * Not possible in Z, intended for the convenience of code using ZTuples.
   */
  public ZTuple()
  {
    tuple_ = new Vector();
  };
  /**
   * Construct a tuple containing two values.
   * @param a The first value.
   * @param b The second value.
   */
  public ZTuple(ZValue a, ZValue b)
  {
    tuple_ = new Vector();
    tuple_.add(a);
    tuple_.add(b);
  };
  /**
   * Construct a tuple from a list of values.
   * @param tuple The list of values.
   */
  public ZTuple(List/*<ZValue>*/ tuple)
  {
    tuple_ = new Vector(tuple);
  };

  /**
   * @return An iterator over the values in the tuple.
   */
  public Iterator iterator()
  {
    return tuple_.iterator();
  };
  /**
   * @return The number of values in the tuple.
   */
  public int size()
  {
    return tuple_.size();
  };
  /**
   * Return the <code>index</code>th value in the tuple.
   * @param index Index into the tuple.
   * @return The value at location <code>index</code>.
   */
  public ZValue get(int index)
  {
    return (ZValue) tuple_.get(index);
  };

  /**
   * @return a <code>String</code> representation of the tuple.
   */
  public String toString()
  {
    String result = "( ";
    Iterator it = iterator();
    if (it.hasNext()) result += it.next();
    while (it.hasNext()) result += " , " + it.next();
    result += " )";
    return result;
  };

  /**
   * Test equality with another object.
   * @param obj The object to compare against.
   * @return <code>true</code> if obj is a tuple with the same values in the
   *         same order.
   */
  public boolean equals(Object obj)
  {
    return obj instanceof ZTuple && ((ZTuple) obj).tuple_.equals(tuple_);
  };
  /**
   * @return this object's hashcode.
   */
  public int hashCode()
  {
    return tuple_.hashCode();
  };
};
