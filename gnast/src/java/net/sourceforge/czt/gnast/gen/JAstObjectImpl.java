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

import java.util.*;
import java.util.logging.Logger;

/**
 * <p>An abstract AST object.  This class provides a skeleton
 * implementation of the JAstObject interface to minimize the effort
 * required to implement this interface.</p>
 *
 * <p>To implement a concrete AST object,
 * the programmer needs to extend this class and provide
 * implements for the <code>getName()</code> and <code>getProject</code>
 * methods.</p>
 *
 * <p>If the concrete AST object provides properties, the
 * programmer needs to overwrite methods <code>getProperties()</code>
 * and <code>getInheritedProperties()</code>.
 *
 * @author Petra Malik
 */
public abstract class JAstObjectImpl implements JAstObject
{
  private static String sClassName = "JAstObjectImpl";
  private static Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast.gen." + sClassName);

  public abstract String getName();

  public String getFullName()
  {
    return getPackage() + "." + getName();
  }

  /**
   * Returns the same as {@link #getName}.
   *
   * @return the value of {@link #getName}.
   */
  public String getImplName()
  {
    return getName();
  }

  /**
   * Returns the empty string.
   *
   * @return the empty string.
   */
  public String getPackage()
  {
    return "";
  }

  /**
   * Returns the value of getPackage().
   */
  public String getImplPackage()
  {
    return getPackage();
  }

  /**
   * Returns <code>null</code>.
   *
   * @return <code>null</code>.
   */
  public String getExtends()
  {
    return null;
  }

  /**
   * Returns the same as {@link #getExtends()}.
   */
  public String getImplExtends()
  {
    return getExtends();
  }

  /**
   * Returns <code>false</code>.
   *
   * @return <code>false</code>.
   */
  public boolean getAbstract()
  {
    return false;
  }

  /**
   * Returns <code>null</code>.
   *
   * @return <code>null</code>.
   */
  public List getProperties()
  {
    return null;
  }

  /**
   * Returns a list containing the results of {@link #getProperties}
   * followed by {@link #getInheritedProperties}.
   *
   * @return <code>null</code> if {@link #getProperties}
             or {@link #getInheritedProperties}
   *         returns <code>null</code>.
   */
  public List getAllProperties()
  {
    String methodName = "getAllProperties";
    sLogger.entering(sClassName, methodName);

    List result = getProperties();
    List inhProps = getInheritedProperties();
    if (inhProps == null) {
      result = null;
    } else if (result != null) {
      result.addAll(inhProps);
    }

    sLogger.exiting(sClassName, methodName, result);
    return result;
  }

  /**
   * Returns <code>null</code>.
   *
   * @return <code>null</code>.
   */
  public List getInheritedProperties()
  {
    return null;
  }
}
