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
import java.util.logging.Logger;

/**
 * A simple debug proxy.
 *
 * @author Petra Malik
 */
public final class DebugProxy
  implements java.lang.reflect.InvocationHandler
{
  /**
   * The object for which debugging information is provided.
   */
  private Object object_;

  private DebugProxy(Object object)
  {
    getLogger().fine("Create new DebugProxy for " + object);
    object_ = object;
  }

  private Logger getLogger()
  {
    return Logger.getLogger("debug");
  }

  public static Object newInstance(Object object)
  {
    return Proxy.newProxyInstance(object.getClass().getClassLoader(),
                                  object.getClass().getInterfaces(),
                                  new DebugProxy(object));
  }

  public Object invoke(Object proxy, Method m, Object[] args)
    throws Throwable
  {
    Object result = null;
    if (args != null) {
      getLogger().entering(object_.getClass().toString(), m.getName(), args);
    }
    else {
      getLogger().entering(object_.getClass().toString(), m.getName());
    }
    try {
      result = m.invoke(object_, args);
    }
    catch (InvocationTargetException e) {
      throw e.getTargetException();
    }
    catch (Exception e) {
      getLogger().fine("Caught exception " + e);
      throw e;
    }
    finally {
      getLogger().exiting(object_.getClass().toString(), m.getName(), result);
    }
    return result;
  }
}
