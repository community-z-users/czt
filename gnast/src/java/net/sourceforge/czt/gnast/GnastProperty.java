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
 * A Gnast property.
 * A Gnast property is similar to a simple property of
 * a JavaBean; it is a <code>private</code> value within
 * a java class (here within a Gnast class) which can be
 * accessed through <code>getter</code> and
 * <code>setter</code> methods.
 *
 * @author Petra Malik
 */
public interface GnastProperty extends GnastVariable
{
  String getName();

  /**
   * Returns the name of the getter for this property.
   * @return the name of the getter for this property.
   */
  String getGetterName();

  /**
   * Returns the name of the setter for this property.
   * @return the name of the setter for this property.
   */
  String getSetterName();

  /**
   * Returns the name of the member variable for this property.
   * @return the name of the member variable for this property.
   */
  String getMemVarName();

  boolean getImmutable();
  boolean getAttribute();
}
