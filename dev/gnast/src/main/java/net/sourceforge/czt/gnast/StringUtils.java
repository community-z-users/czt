/**
Copyright 2003 Petra Malik
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

package net.sourceforge.czt.gnast;

/**
 * An utility class that performs operations on Strings.
 *
 * @author Petra Malik
 */
public final class StringUtils
{
  /**
   * Do not instanciate this class.
   */
  private StringUtils()
  {
  }

  /**
   * Capitalizes the first character of the given String.
   *
   * @param str the String to capitalize, may be <code>null</code>.
   * @return capitalized String, <code>null</code> if the input String
   *         is <code>null</code>.
   */
  public static String capitalize(String str)
  {
    if (str == null || str.length() < 1) return str;
    return str.substring(0, 1).toUpperCase() + str.substring(1);
  }
}
