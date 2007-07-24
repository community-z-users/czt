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

import net.sourceforge.czt.animation.eval.result.GivenValue;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
 * Class representing the value of a Z variable of type Given.
 */
public class ZGiven implements ZValue
{
  //private final String value_;
  private final ZName ex_; // Proxy to ZName

  private final GivenValue expr_;// But ZName is not a Expr, so use GivenValue

  // For unique reference, we need to keep it here.
  private static Factory factory_;

  /**
   * Create a new <code>ZGiven</code> with its value set to <code>value</code>.
   * @param value The value to store in the <code>ZGiven</code>.
   */
  public ZGiven(String value)
  {
    //value_ = value;
    factory_ = GaffeFactory.getFactory();
    ex_ = factory_.createZName(value);
    expr_ = new GivenValue(value);
  }

  /**
   * Create a new <code>ZGiven</code> from a <code>ZName</code>
   * @param expr_ the ZName used to created the corresponding ZGiven.
   */
  public ZGiven(GivenValue expr)
  {
    factory_ = GaffeFactory.getFactory();
    ex_ = factory_.createZName(expr.getValue());
    expr_ = expr;
  }

  /**
   * Getter method for the <code>ZGiven</code>'s value.
   * @return The value stored in the ZGiven.
   */
  public String getValue()
  {
    //return value_;
    return ex_.getWord();
  }

  /**
   * Returns string representation of the ZGiven.
   * (Same result as {@link #getValue}).
   * @return The string representation of the object.
   */
  public String toString()
  {
    //return value_;
    return ex_.getWord();
  }

  /**
   * Tests if the ZGiven is equal to another object.
   * @param obj The object to compare this one against.
   * @return <code>true</code> if <code>obj</code> is a <code>ZGiven</code> with
   *         the same value as this <code>ZGiven</code>.
   */
  public boolean equals(Object obj)
  {
    return obj instanceof ZGiven && toString().equals(obj.toString());
  }

  /**
   * @return Hash code for this object.
   */
  public int hashCode()
  {
    //return value_.hashCode();
    return ex_.hashCode();
  }

  /**
   * Get the expr type representing the zvalue
   * @return the representing expr
   */
  public GivenValue getExpr()
  {
    return expr_;
  }
}
