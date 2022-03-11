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

package net.sourceforge.czt.parser;

import java.net.URL;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.zml.Resources;

/**
 * A class that converts example names to valid URLs.
 *
 * @author Petra Malik
 */
public final class Examples
{
  private static Examples examples_ = new Examples();

  /**
   * Do not create instances of this class.
   */
  private Examples()
  {
  }

  public static URL getExample(String name)
  {
    URL result = Resources.getZExample(name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }

  public static URL getTestExample(String name)
  {
    URL result = examples_.getClass().getResource("/tests/z/" + name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }
}
