/*
  Copyright 2003, 2005, 2007 Petra Malik
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

import java.util.List;

/**
 * <p>
 * An abstract representation of an AST interface
 * together with its implementation.
 * </p>
 *
 * <p>If it represents an interface without an implementing
 * class, getImplName returns null.
 * If it represents a class without an interface,
 * getName() is equal to getImplName().
 * In this case, getPackage() should be equal to getImplPackage()
 * and getExtends() should be equal to getImplExtends() to
 * avoid confusion.
 * If it represents both (an interface together with its
 * implementing class), getName() should not be equal to
 * getImplName().</p>
 *
 * @author Petra Malik
 * @czt.todo Check the Javadoc documentation.  Does it really
 *           happen that this is used for an interface without
 *           an implementation?
 */
public interface JAstObject extends JObject
{
  /**
   * Returns whether the corresponding XML schema
   * element has a type similar to its name.
   */
  boolean getNameEqualsType();


  String getVisitorPackage();
  
  /**
   * <p>Returns the class (or implementation) name
   * of this Gnast class.</p>
   *
   * <p>If an interface together with its implementation
   * is represented by this Gnast class, method
   * #getName returns the name of the interface
   * and this method returns the name of the implementing
   * class.</p>
   *
   * @return the class name of this Gnast class,
   *         or <code>null</code> if the name
   *         is not known or undefined.
   */
  String getImplName();

  /**
   * Returns whether this Gnast class is abstract or not.
   *
   * @return <code>true</code> if this Gnast class is abstract;
   *         <code>false</code> otherwise.
   */
  boolean getAbstract();

  /**
   * Returns the package name of the implemeting class
   * of this Gnast class.
   *
   * @return the package name of the implementing class
   *         of this Gnast class,
   *         or <code>null</code> if the implementing class
   *         name is unknown or undefined.
   */
  String getImplPackage();

  String getExtends();
  boolean isInstanceOf(String name);

  String getImplExtends();

  /**
   * Returns the property list of this Gnast class.
   * This list does not include inherited properties.
   *
   * @return a list of properties (objects of type
   *         {ref GnastProperty}).
   */
  List<Object> getProperties();

  /**
   * Returns a list of all properties for this Gnast class.
   * This list does include inherited properties.
   *
   * @return a list of all properties (objects of type
   *         {ref GnastProperty}).
   */
  List<Object> getAllProperties();

  /**
   * Returns a list of inherited properties for this Gnast class.
   *
   * @return a list of all inherited properties (objects of type
   *         {ref GnastProperty}).
   */
  List<Object> getInheritedProperties();

  String getJavadoc();

  String getAdditionalCodeFilename();

  String getAdditionalImplCodeFilename();

  boolean isList();

  String getNamespace();
  
  /**
   * Check whether the enum name type given is known within the name space or not.
   * @param type
   * @return
   */
  boolean isKnownEnumeration(String type);
}
