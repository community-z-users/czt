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
 * Class representing the value of a Z variable of type Given.
 */
public class ZGiven implements ZValue
{
  private final String value_;

  /**
   * Create a new <code>ZGiven</code> with its value set to <code>value</code>.
   * @param value The value to store in the <code>ZGiven</code>.
   */
  public ZGiven(String value)
  {
    value_ = value;
  };

  /**
   * Getter method for the <code>ZGiven</code>'s value.
   * @return The value stored in the ZGiven.
   */
  public String getValue()
  {
    return value_;
  };
  /**
   * Returns string representation of the ZGiven.
   * (Same result as {@link #getValue}).
   * @return The string representation of the object.
   */
  public String toString()
  {
    return value_;
  };
  /**
   * Tests if the ZGiven is equal to another object.
   * @param obj The object to compare this one against.
   * @return <code>true</code> if <code>obj</code> is a <code>ZGiven</code> with
   *         the same value as this <code>ZGiven</code>.
   */
  public boolean equals(Object obj)
  {
    return obj instanceof ZGiven && ((ZGiven) obj).value_.equals(value_);
  };
  /**
   * @return Hash code for this object.
   */
  public int hashCode()
  {
    return value_.hashCode();
  };
};
