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
 * An abstract representation of a java class or interface.
 *
 * @author Petra Malik
 */
public class JObjectImpl implements JObject
{
  /**
   * The name of this GnastObject.
   */
  private String mName;

  /**
   * The package name of this GnastObject.
   */
  private String mPackage;

  /**
   * Constructs a new abstract java object
   * with the given name and package name.
   *
   * @param name the name of the GnastObject (must not be <code>null</code>).
   * @param packageName the package name of the GnastObject
   *                    (must not be <code>null</code>).
   * @throws NullPointerException if one of the arguments is <code>null</code>.
   */
  public JObjectImpl(String name, String packageName)
  {
    if (name == null || packageName == null)
      throw new NullPointerException();
    mName = name;
    mPackage = packageName;
  }

  public String getName()
  {
    return mName;
  }

  public String getFullName()
  {
    return getPackage() + "." + getName();
  }

  public String getPackage()
  {
    return mPackage;
  }

  public String toString()
  {
    return "GnastObject(" + mPackage + "." + mName + ")";
  }
}
