/**
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.parser.util;

/**
 * Contains access methods for various settings.
 */
public final class Settings
{
  /**
   * Do not generate instances of this class.
   */
  private Settings()
  {
  }

  /**
   * Returns the czt home directory.
   */
  public static String getCztHome()
  {
    return System.getProperty("czt.home");
  }

  /**
   * Returns the czt lib directory.
   */
  public static String getCztLib()
  {
    String result = System.getProperty("czt.lib");
    if (result == null) {
      result = getCztHome() + "/parser/lib";
    }
    return result;
  }
}
