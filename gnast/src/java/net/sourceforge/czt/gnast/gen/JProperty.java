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
 * <p>
 * An abstract representation of a Java property.
 * </p>
 *
 * <p>
 * A Java property is similar to a simple property of
 * a JavaBean; it is a <code>private</code> value within
 * a Java class which can be accessed through <code>getter</code> and
 * <code>setter</code> methods.
 * </p>
 *
 * @author Petra Malik
 */
public interface JProperty extends JVariable
{
  /**
   * Returns the name of this property.
   * @return the name of this property.
   */
  public String getName();

  /**
   * Returns the name of the getter for this property.
   * @return the name of the getter for this property.
   */
  public String getGetterName();

  /**
   * Returns the name of the setter for this property.
   * @return the name of the setter for this property.
   */
  public String getSetterName();

  /**
   * Returns the name of the member variable for this property.
   * @return the name of the member variable for this property.
   */
  public String getMemVarName();

  /**
   * <p>
   * Returns whether this property is an attribute
   * in the XML representation.
   * </p>
   * <p>
   * This information is used for generating XML parsers
   * and serializers like the DOM serializer.  If this
   * method returns <code>true</code> an attribute is parsed
   * (or created), otherwise a node is parsed (or created).
   * </p>
   * @return <code>true</code> if this property is an attribute
   *         in the XML representation;
   *         <code>false</code> otherwise.
   */
  public boolean getAttribute();

  public boolean isReference();
}
