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
 * An implementation of {@link JObject}.
 *
 * @author Petra Malik
 */
public class JObjectImpl implements JObject
{
  /**
   * The name of the represented Java object.
   */
  private String mName;

  /**
   * The package name of the represented Java object.
   */
  private String mPackage;

  /**
   * <p>
   * Constructs a new abstract Java object
   * with the given name and package name.
   * </p>
   *
   * @param name the name of the represented Java object
   *             (must not be <code>null</code>).
   * @param packageName the package name of the represented Java object
   *                    (must not be <code>null</code>).
   * @throws NullPointerException if one of the arguments is <code>null</code>.
   * @czt.todo Check whether the given parameters are
   *                 valid Java names.
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

  /**
   * Returns a string representation of this object
   * containing name and package name information of
   * the represented Java class or interface.
   */
  public String toString()
  {
    return "JObjectImpl(" + mPackage + "." + mName + ")";
  }
}
