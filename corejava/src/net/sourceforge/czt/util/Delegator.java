/**
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.util;

import java.lang.reflect.*;
import java.util.*;
import java.util.logging.Logger;

/**
 * A simple delegator.
 *
 * @author Petra Malik
 */
public class Delegator
  implements java.lang.reflect.InvocationHandler
{
  private Map mMap = new HashMap();

  /**
   * @see #newInstance
   */
  private Delegator(Class[] interfaces, Object[] impls)
  {
    if (interfaces.length != impls.length) {
      throw new IllegalArgumentException();
    }
    for (int i = 0; i < interfaces.length; i++) {
      if (! interfaces[i].isAssignableFrom(impls[i].getClass())) {
	throw new IllegalArgumentException(impls[i].getClass().toString()
					   + " is not an instance of "
					   + interfaces[i].toString());
      }
      Method[] methods = interfaces[i].getMethods();
      for (int j = 0; j < methods.length; j++) {
	String methodName = methods[j].getName();
	if (mMap.get(methodName) != null && mMap.get(methodName) != impls[i]) {
	  String message = methodName
	    + " is defined in more than one interface.";
	  throw new IllegalArgumentException(message);
	}
	mMap.put(methodName, impls[i]);
      }
    }
  }
  
  /**
   * @throws NullPointerException if <code>interfaces</code> or
   *         <code>impls</code> is <code>null</code>.
   * @throws IllegalArgumentException if the length of the two
   *         given arrays <code>interfaces</code> and
   *         <code>implementations</code>is not equal, there is the
   *         same method name defined in two or more interfaces, or
   *         <code>implementations[i]</code> does not implement
   *         <code>interfaces[i]</code>.
   */
  public static Object newInstance(Class[] interfaces,
				   Object[] implementations)
  {
    return Proxy.newProxyInstance(interfaces[0].getClassLoader(),
				  interfaces,
				  new Delegator(interfaces, implementations));
  }
  
  public Object invoke(Object proxy, Method m, Object[] args)
    throws Throwable
  {
    Object impl = mMap.get(m.getName());
    if (impl != null) {
      return m.invoke(impl, args);
    }
    throw new InternalError("Delegator: unexpected method dispatched: " + m);
  }
}
