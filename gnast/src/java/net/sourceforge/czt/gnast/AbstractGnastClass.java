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

import java.util.*;
import java.util.logging.Logger;

/**
 * An abstract Gnast class.
 * Methods that must be implemented by a deriving class in order
 * to implement GnastClass: getName().
 * To get properties working, it is sufficient to overwrite
 * getProperties() and getInheritedProperties().
 *
 * This class does:
 *   * getImplName() := getName()
 *   * getAbstract() := false
 *   * getPackage() := ""
 *   * getImplPackage() := getPackage()
 *   * getImplExtends := getExtends() := null
 *   * getProperties() := null
 *   * ...
 *
 * @author Petra Malik
 */
public abstract class AbstractGnastClass implements GnastClass
{
  private static String sClassName = "AbstractGnastClass";
  private static Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast." + "." + sClassName);

  /**
   * Returns the value of <code>getName()</code>.
   */
  public String getImplName()
  {
    return getName();
  }

  /**
   * Returns the empty string.
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
   * Returns the value of getImplExtends().
   */
  public String getImplExtends()
  {
    return getExtends();
  }

  /**
   * Returns always <code>false</code>
   *
   * @return <code>false</code>.
   */
  public boolean getAbstract()
  {
    return false;
  }

  /**
   *
   * @throws ClassCastExpection if the list contains an
   *         element that is not a property.
   */
  private List collectImmutableProperties(List propList)
  {
    List erg = null;
    if(propList != null) {
      erg = new ArrayList();
      for(Iterator iter=propList.iterator(); iter.hasNext();) {
	GnastProperty prop = (GnastProperty) iter.next();
	if(prop.getImmutable()) {
	  erg.add(prop);
	}
      }
    }
    return erg;
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

  public List getImmutableProperties()
  {
    return collectImmutableProperties(getProperties());
  }

  public List getAllProperties()
  {
    String methodName = "getAllProperties";
    sLogger.entering(sClassName, methodName);
    List props = getProperties();
    List inhProps = getInheritedProperties();
    if (props == null || inhProps == null) return null;
    props.addAll(inhProps);
    sLogger.exiting(sClassName, methodName, props);
    return props;
  }

  public List getAllImmutableProperties()
  {
    return collectImmutableProperties(getAllProperties());
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

  public List getInheritedImmutableProperties()
  {
    return collectImmutableProperties(getInheritedProperties());
  }
}
