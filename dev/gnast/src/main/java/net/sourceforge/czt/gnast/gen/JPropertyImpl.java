/*
  Copyright 2003, 2007 Petra Malik
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
 * <p>An abstract Java property.  This class provides a skeleton
 * implementation of the JProperty interface to minimize the effort
 * required to implement this interface.</p>
 *
 * <p>To implement a concrete Java property, the programmer needs
 * to extend this class and provide implementations for the
 * <code>getName()</code>, ...
 * methods.</p>
 *
 * @author Petra Malik
 */
public abstract class JPropertyImpl implements JProperty
{
  public String toString()
  {
    return "JProperty " + getName();
  }

  public String getLName()
  {
    String name = getName();
    return name.substring(0,1).toLowerCase() + name.substring(1);
  }

  /**
   * Returns the name of the getter for this property.
   * @return the name of the getter for this property.
   */
  public String getGetterName()
  {
    return "get" + getName();
  }

  /**
   * Returns the name of the setter for this property.
   * @return the name of the setter for this property.
   */
  public String getSetterName()
  {
    return "set" + getName();
  }

  public String getVarName()
  {
    return getName().substring(0, 1).toLowerCase() + getName().substring(1);
  }

 /**
   * Returns the name of the member variable for this property.
   * @return the name of the member variable for this property.
   */
  public String getMemVarName()
  {
    return getVarName() + "_";
  }

  public boolean isReference()
  {
    return true;
  }
}
