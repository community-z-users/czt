/**
Copyright (C) 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.result;

import net.sourceforge.czt.base.ast.Term;


/** A member of a given set.
 *
 * @author marku
 *
 * @see net.sourceforge.czt.animation.eval.flatpred.FlatGivenSet
 */
public class GivenValue extends EvalResult
{
  private String value_;

  public GivenValue(String value)
  {
    value_ = value;
  }

  public String getValue()
  {
    return value_;
  }

  public int hashCode()
  {
    return 371 ^ value_.hashCode();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof GivenValue)
      return value_.equals( ((GivenValue)obj).value_ );
    else
      return false;
  }
  
  @Override
  public String toString()
  {
    return value_;
  }
  
  /** {@inheritDoc}
   *  EvalResult provides a default implementation of
   *  getChildren that returns an empty array of children.
   */
  public Object[] getChildren()
  {
    return new Object[0];
  }

  /** {@inheritDoc}
   *  EvalResult provides a default implementation of
   *  create that throws UnsupportedOperationException.
   */
  public Term create(Object[] args)
  {
    return this; // GivenValues are like constants
  }
}
