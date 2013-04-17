/**
Copyright (C) 2003, 2004 Mark Utting
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

/**
 * A simple delegator.
 *
 * @author Petra Malik
 */
public final class Delegator
  implements InvocationHandler
{
  private final Map<String, Object> map_ = new HashMap<String, Object>();

  /**
   * Creates a new delegator.
   *
   * @see #newInstance
   */
  private Delegator(Class<?>[] interfaces, Object[] impls)
  {
    if (interfaces == null || impls == null) {
      throw new NullPointerException();
    }
    if (interfaces.length != impls.length) {
      throw new IllegalArgumentException();
    }
    for (int i = 0; i < interfaces.length; i++) {
      if (interfaces[i] == null || impls[i] == null) {
        throw new NullPointerException();
      }
      if (!interfaces[i].isAssignableFrom(impls[i].getClass())) {
        throw new IllegalArgumentException(impls[i].getClass().toString()
                                           + " is not an instance of "
                                           + interfaces[i].toString());
      }
      Method[] methods = interfaces[i].getMethods();
      for (int j = 0; j < methods.length; j++) {
        String methodName = methods[j].getName();
        if (map_.get(methodName) != null && map_.get(methodName) != impls[i]) {
          String message = methodName
            + " is defined in more than one interface.";
          throw new IllegalArgumentException(message);
        }
        map_.put(methodName, impls[i]);
      }
    }
  }

  /**
   * @throws NullPointerException if <code>interfaces</code> or
   *         <code>implementatations</code> is <code>null</code>,
   *         or <code>interfaces[i]</code> or <code>implementations[i]</code>
   *         is <code>null</code> for some <code>0 &lt; i &lt; size</code>
   *         where <code>size</code> is the size of the corresponding
   *         array.
   * @throws IllegalArgumentException if the length of the two
   *         given arrays <code>interfaces</code> and
   *         <code>implementations</code>is not equal, there is the
   *         same method name defined in two or more interfaces, or
   *         <code>implementations[i]</code> does not implement
   *         <code>interfaces[i]</code>.
   */
  public static Object newInstance(Class<?>[] interfaces,
                                   Object[] implementations)
  {
    ClassLoader classLoader = null;
    if (interfaces.length > 0) {
      classLoader = interfaces[0].getClassLoader();
    }
    return Proxy.newProxyInstance(classLoader,
                                  interfaces,
                                  new Delegator(interfaces, implementations));
  }

  public Object invoke(Object proxy, Method m, Object[] args)
    throws Throwable
  {
    Object impl = map_.get(m.getName());
    if (impl != null) {
      return m.invoke(impl, args);
    }
    throw new CztException("Delegator: unexpected method dispatched: " + m);
  }
}
