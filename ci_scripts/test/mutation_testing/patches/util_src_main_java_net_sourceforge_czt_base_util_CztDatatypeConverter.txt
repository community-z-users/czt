/*
  Copyright 2003, 2006 Mark Utting
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

package net.sourceforge.czt.base.util;

import net.sourceforge.czt.base.ast.Digit;

/**
 * @author Petra Malik
 */
public final class CztDatatypeConverter
{
  /**
   * Do not create instances of this class.
   */
  private CztDatatypeConverter()
  {
  }

  public static Digit parseDigit(String s)
  {
    return Digit.fromValue(Integer.parseInt(s));
  }

  public static String printDigit(Digit digit)
  {
    return "" + digit.getValue();
  }

  public static Boolean parseBoolean(String s)
  {
    return Boolean.valueOf(s);
  }

  public static String printBoolean(Boolean b)
  {
    return  b.toString();
  }
}
