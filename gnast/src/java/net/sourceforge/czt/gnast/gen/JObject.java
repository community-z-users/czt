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
   * Returns the name of this object.  This should be a valid
   * Java class or interface name, but there is currently no
   * check to ensure this.
   *
   * @return the name of this object
   *         (should never be <code>null</code>).
   */
  String getName();

  /**
   * Returns the name of this object, including the package name,
   * as it is used in Java programs; for example, "java.util.List".
   *
   * @return the name of this object, including the package name
   *         (should never be <code>null</code>).
   */
  String getFullName();

  /**
   * Returns the package name of this object as it is used in Java;
   * for instance "java.util".
   *
   * @return the package name of this object
   *         (should never be <code>null</code>).
   */
  String getPackage();

  /**
   * Returns the project to which this object belongs to.
   * If the class or interface is part of the Java API, like
   * java.util.List, <code>null</code> is returned.
   *
   * @return the project to which this object belongs to,
   *         <code>null</code> if it does not belong to particular project.
   */
  JProject getProject();
}
