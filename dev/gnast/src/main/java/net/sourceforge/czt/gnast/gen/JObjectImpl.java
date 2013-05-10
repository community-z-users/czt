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
  private String name_;

  /**
   * The package name of the represented Java object.
   */
  private String packageName_;

  /**
   * The project to which that object belongs to.
   */
  private JProject project_;

  public JObjectImpl(String name)
  {
    this(name, "", null);
  }

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
    this(name, packageName, null);
  }

  /**
   * <p>
   * Constructs a new abstract Java object
   * with the given name, package name, and project.
   * </p>
   *
   * @param name the name of the represented Java object
   *             (must not be <code>null</code>).
   * @param packageName the package name of the represented Java object
   *                    (must not be <code>null</code>).
   * @throws NullPointerException if <code>name</code> or
   *         <code>packageName</code> is <code>null</code>.
   */
  public JObjectImpl(String name, String packageName, JProject project)
  {
    if (name == null || packageName == null)
      throw new NullPointerException();
    name_ = name;
    packageName_ = packageName;
    project_ = project;
  }

  public String getName()
  {
    return name_;
  }

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
    	System.err.println("JObject getFullName() = " + result);
    }
    // if some package, then set that to the result directly
    else 
    {
    	result = packageName + "." + getName();
    }
    return result;
  }

  public String getPackage()
  {
    return packageName_;
  }

  public JProject getProject()
  {
    return project_;
  }

  /**
   * Returns a string representation of this object
   * containing name and package name information of
   * the represented Java class or interface.
   */
  public String toString()
  {
    return getFullName();
  }
}
