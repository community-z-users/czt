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

package net.sourceforge.czt.gnast.gen;

/**
 * An abstract representation of a Java class or interface.
 *
 * @author Petra Malik
 */
public interface JObject
{
  /**
   * Returns the name of this Object.
   *
   * @return the name of this Object
   *         (should never be <code>null</code>).
   */
  public String getName();

  /**
   * Returns the name of this Object, including the package name.
   *
   * @return the name of this Object, including the package name
   *         (should never be <code>null</code>).
   */
  public String getFullName();

  /**
   * Returns the package name of this Object.
   *
   * @return the package name of this Gnast class
   *         (should never be <code>null</code>).
   */
  public String getPackage();
}
