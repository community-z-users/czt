/*
  Copyright 2003, 2006, 2012  Petra Malik, Andrius Velykis
  
  This file is part of the CZT project.

  The CZT project is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT.  If not, see <http://www.gnu.org/licenses/>.
*/

package net.sourceforge.czt.gnast.gen;

import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.gnast.GlobalProperties;


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
 * @author Andrius Velykis
 */
public abstract class JAstObjectImpl implements JAstObject
{
  private GlobalProperties global_;
  private static final String CLASS_NAME = "JAstObjectImpl";
  private static final Logger LOGGER =
    Logger.getLogger("net.sourceforge.czt.gnast.gen." + CLASS_NAME);

  public JAstObjectImpl(GlobalProperties global)
  {
    global_ = global;
  }

  public abstract String getName();

  public String getFullName()
  {
	  // for some reason (dunno exactly) in some ListType cases packageName is already in Name.
    String packageName = getPackage();
    String result;
    // if package already in name, return the name
    if (getName().startsWith(packageName))
    	result = getName();
    // if no package
    else if ("".equals(packageName)) 
    {
    	// check project: if present extract package
    	if (getProject() != null)
    	{
    		// extract the appropriate package depending on the name
    		result = (getName().endsWith("Impl") ? 
    					getProject().getImplPackage() :
    					getProject().getAstPackage()) + "." + getName();
    	}
    	// otherwise just use the name
    	else
    	{
    		result = getName();
    	}
    	//System.err.println("JObject getFullName() = " + result);
    }
    // if some package, then set that to the result directly
    else 
    {
    	result = packageName + "." + getName();
    }
    return result;
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
  public List<Object> getProperties()
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
  public List<Object> getAllProperties()
  {
    String methodName = "getAllProperties";
    LOGGER.entering(CLASS_NAME, methodName);

    List<Object> props = getProperties();
    List<Object> inhProps = getInheritedProperties();
    if (props == null || inhProps == null)
      return null;

    List<Object> result = new ArrayList<Object>(inhProps.size() + props.size());
    result.addAll(inhProps);
    result.addAll(props);

    LOGGER.exiting(CLASS_NAME, methodName, result);
    return result;
  }

  /**
   * Returns <code>null</code>.
   *
   * @return <code>null</code>.
   */
  public List<Object> getInheritedProperties()
  {
    return null;
  }

  public String getAdditionalCodeFilename()
  {
    return global_.resolvePath(getName() + ".java");
  }

  public String getAdditionalImplCodeFilename()
  {
    return global_.resolvePath(getImplName() + ".java");
  }

  public abstract String getNamespace();
}
