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

/**
 * Values in Z that are numbers.
 */
public class ZNumber implements ZValue
{
  private final long number_;

  /**
   * Construct a <code>ZNumber</code> set to a specific value.
   * @param number The value to store.
   */
  public ZNumber(long number)
  {
    number_ = number;
  };

  /**
   * Getter method for the number value.
   * @return the value.
   */
  public long getNumber()
  {
    return number_;
  };
  /**
   * @return A string representation of the number.
   */
  public String toString()
  {
    return "" + number_;
  };

  /**
   * Compare for equality against another object.
   * @param obj The object to compare against.
   * @return <code>true</code> if <code>obj</code> is a <code>ZNumber</code>
   *         with the same value stored.
   */
  public boolean equals(Object obj)
  {
    return obj instanceof ZNumber && ((ZNumber) obj).number_ == number_;
  };
  /**
   * @return This object's hashcode.
   */
  public int hashCode()
  {
    return (int) number_;
  };
};
