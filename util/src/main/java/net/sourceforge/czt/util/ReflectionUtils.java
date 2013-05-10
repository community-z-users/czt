/*
  Copyright 2007 Mark Utting
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

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import net.sourceforge.czt.base.util.PerformanceSettings;

/**
 *
 * @author leo
 */
public final class ReflectionUtils
{
  /** Do not create instances of this class. */
  private ReflectionUtils()
  {
  }

  public static List<Class<?>> transitiveSuperClasses(Object o)
  {
    return transitiveSuperClasses(o.getClass().getSuperclass());
  }

  public static List<Class<?>> reflexiveTransitiveSuperClasses(Object o)
  {
    return transitiveSuperClasses(o.getClass());
  }

  public static List<Class<?>> transitiveSuperClasses(Class<?> cls)
  {
    List<Class<?>> result = new ArrayList<Class<?>>(PerformanceSettings.INITIAL_ARRAY_CAPACITY * 2);
    Class<?> aClass = cls;
    while (aClass != null) {
      if (!result.contains(aClass)) {
        result.add(aClass);
      }
      aClass = aClass.getSuperclass();
    }
    return result;
  }

  protected static List<Class<?>> transitiveInterfaces(Class<?>... cls)
  {
    List<Class<?>> result = new ArrayList<Class<?>>(cls.length);
    List<Class<?>> partialResult;
    for (Class<?> intf : cls) {
      partialResult = transitiveInterfaces(intf.getInterfaces());
      for (Class<?> superIntf : partialResult) {
        if (!result.contains(superIntf)) {
          result.add(superIntf);
        }
      }
      if (!result.contains(intf)) {
        result.add(intf);
      }
    }
    return result;
  }

  public static List<Class<?>> reflexiveTransitiveInterfaces(Object o)
  {
    return transitiveInterfaces(o.getClass());
  }

  public static List<Class<?>> transitiveInterfaces(Object o)
  {
    return transitiveInterfaces(o.getClass().getSuperclass());
  }

  public static List<Class<?>> transitiveInterfaces(Class<?> cls)
  {
    List<Class<?>> result = new ArrayList<Class<?>>(PerformanceSettings.INITIAL_ARRAY_CAPACITY * 2);
    List<Class<?>> partialResult;
    Class<?> aClass = cls;
    while (aClass != null) {
      partialResult = transitiveInterfaces(aClass.getInterfaces());
      for (Class<?> intf : partialResult) {
        if (!result.contains(intf)) {
          result.add(intf);
        }
      }
      aClass = aClass.getSuperclass();
    }
    return result;
  }

  public static Set<Method> getAllMethodsFrom(Object o, String startingWith)
  {
    // collect all super classes up to Object considering o itself
    List<Class<?>> superCls = reflexiveTransitiveSuperClasses(o);
    Set<Method> allPublicMethods = new HashSet<Method>();
    for (Class<?> cls : superCls) {
      for (Method m : cls.getMethods()) {
      //for (Method m : o.getClass().getMethods()) {
        if (m.getName().startsWith(startingWith)) {
          allPublicMethods.add(m);
        }
      }
    }
    return allPublicMethods;
  }

  public static Set<Class<?>> getAllInterfacesFrom(Object o, String endingWith)
  {
    // collect all super classes up to Object considering o itself
    List<Class<?>> superIntf = reflexiveTransitiveInterfaces(o);
    Set<Class<?>> allInterfaces = new HashSet<Class<?>>();
    for (Class<?> cls : superIntf) {
      if (cls.getName().endsWith(endingWith)) {
        allInterfaces.add(cls);
      }
    }
    return allInterfaces;
  }
}
