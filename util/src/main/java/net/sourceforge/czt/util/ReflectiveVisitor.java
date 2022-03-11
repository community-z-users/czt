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
import java.util.logging.*;

/**
 * An abstract implementation of a reflective visitor.
 *
 * @author Petra Malik
 */
public abstract class ReflectiveVisitor
{
  private String getClassName()
  {
    return "ReflectiveVisitor";
  }

  private Logger getLogger()
  {
    return Logger.getLogger("net.sourceforge.czt.util." + getClassName());
  }

  /**
   * Invokes the method that fits best.
   * If the invoke returns an exception,
   * the error trace is printed and <code>null</code>
   * is returned.  If the exception is a RuntimeException,
   * it is not catched.
   * Idee: how about returning the exception?
   */
  public Object dispatch(Object o)
  {
    if (o == null) {
      return null;
    }
    try {
      Method method = getMethod(o.getClass());
      return method.invoke(this, new Object[] {o});
    }
    catch (InvocationTargetException e) {
      getLogger().finer("Caught InvocationTargetException");
      Throwable throwable = e.getCause();
      if (throwable instanceof Error) {
        throw (Error) throwable;
      }
      else if (throwable instanceof RuntimeException) {
        throw (RuntimeException) throwable;
      }
      else {
        e.printStackTrace();
      }
    }
    catch (IllegalAccessException e) {
      getLogger().finer("Caught IllegalAccessException");
      Throwable throwable = e.getCause();
      if (throwable instanceof Error) {
        throw (Error) throwable;
      }
      else if (throwable instanceof RuntimeException) {
        throw (RuntimeException) throwable;
      }
      else {
        e.printStackTrace();
      }
    }
    return null;
  }

  protected Method getMethod(Class<?> c)
  {
    final String methodName = "getMethod";
    getLogger().entering(getClassName(), methodName, c);

    Method m = null;
    Class<?> newc = c;
    while (m == null && newc != Object.class) {
      String method = newc.getName();
      method = "visit" + method.substring(method.lastIndexOf('.') + 1);
      getLogger().finer("Try " + newc.toString());
      try {
        m = getClass().getMethod(method, new Class[] {newc});
      }
      catch (NoSuchMethodException e) {
        getLogger().finer("Caught NoSuchMethodException");
      }
      if (m == null) { m = tryInterfaces(newc); }
      newc = newc.getSuperclass();
    }
    if (m == null) {
      try {
        m = getClass().getMethod("visitObject", new Class[] {Object.class});
      }
      catch (Exception e) {
        e.printStackTrace();
      }
    }
    getLogger().exiting(getClassName(), methodName, m);
    return m;
  }

  protected Method tryInterfaces(Class<?> c)
  {
    final String methodName = "tryInterfaces";
    getLogger().entering(getClassName(), methodName, c);

    String methodPrefix = "visit";
    Method m = null;
    Class<?>[] interfaces = c.getInterfaces();
    for (int i = 0; i < interfaces.length; i++) {
      String method = interfaces[i].getName();
      method = methodPrefix + method.substring(method.lastIndexOf('.') + 1);
      getLogger().finer("Try " + method.toString());
      try {
        m = getClass().getMethod(method, new Class[] {interfaces[i]});
      }
      catch (NoSuchMethodException noSuchMethodException) {
        getLogger().finer("Caught NoSuchMethodException");
      }
      catch (SecurityException securityException) {
        getLogger().finer("Caught SecurityException");
      }
    }
    getLogger().exiting(getClassName(), methodName, m);
    return m;
  }
}
