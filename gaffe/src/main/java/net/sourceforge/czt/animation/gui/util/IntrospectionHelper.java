/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

 This program is free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License
 as published by the Free Software Foundation; either version 2
 of the License, or (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */

package net.sourceforge.czt.animation.gui.util;

import java.beans.BeanInfo;
import java.beans.EventSetDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyDescriptor;
import java.beans.PropertyEditor;
import java.beans.PropertyEditorManager;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.EventListener;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * IntrospectionHelper provides functions for simplifying Introspection on beans
 * in the rest of this project.  Note this is a Singleton class - it can not be
 * instantiated.
 * XXX needs work.
 */
public final class IntrospectionHelper
{
  //Have to keep a strong reference to get around bug #4646747
  //Mentioned here:
  //http://java.sun.com/products/jfc/tsc/articles/persistence4/index.html
  private static final Set<BeanInfo> rememberedBeanInfos = new HashSet<BeanInfo>();

  //Cache is needed because findEditor is too slow to do a lot.
  //Specifically PropertiesTable uses it a lot to determine whether a cell can
  //be edited.
  //Without this cache significant delays happen when creating/switching beans.
  //Even with this cache there are still some delays.
  private static final HashMap<Class<?>, PropertyEditor> editorCache = new HashMap<Class<?>, PropertyEditor>();

  /**
   * Private unused constructor to prevent creation of IntrospectionHelper
   * objects.
   */
  private IntrospectionHelper()
  {
  }

  /**
   * Checks if a bean has a particular property.
   * @param bean The bean to check.
   * @param property The name of the property to check for.
   * @return <code>true</code> if a bean has a particular property.
   */
  public static boolean beanHasProperty(Object bean, String property)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX ???
      return false;
    };

    PropertyDescriptor[] pds = bi.getPropertyDescriptors();
    //PropertyDescriptor pd = null;
    for (int i = 0; i < pds.length; i++) {
      if (pds[i].getName().equals(property)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Tests if a property is readable.
   * @param pd A <code>PropertyDescriptor</code> describing the property.
   * @return <code>true</code> if it is readable.
   */
  public static boolean isReadableProperty(PropertyDescriptor pd)
  {
    return (pd.getReadMethod() != null);
  }

  /**
   * Checks if a bean has a particular property, and it is readable.
   * @param bean The bean to check.
   * @param property The name of the property to check for.
   * @return <code>true</code> if the bean has the given property, and it is
   *         readable.
   */
  public static boolean beanHasReadableProperty(Object bean, String property)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX ???
      return false;
    };
    PropertyDescriptor[] pds = bi.getPropertyDescriptors();
    //PropertyDescriptor pd = null;
    for (int i = 0; i < pds.length; i++)
      if (pds[i].getName().equals(property))
        return isReadableProperty(pds[i]);
    return false;
  }

  /**
   * Tests if a property is writable.
   * @param pd A <code>PropertyDescriptor</code> describing the property.
   * @return <code>true</code> if it is writable.
   */
  public static boolean isWritableProperty(PropertyDescriptor pd)
  {
    return (pd.getWriteMethod() != null);
  }

  /**
   * Checks if a bean has a particular property, and it is writable.
   * @param bean The bean to check.
   * @param property The name of the property to check for.
   * @return <code>true</code> if the bean has the given property, and it is
   *         readable.
   */
  public static boolean beanHasWritableProperty(Object bean, String property)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX ???
      return false;
    };
    PropertyDescriptor[] pds = bi.getPropertyDescriptors();
    //PropertyDescriptor pd = null;
    for (int i = 0; i < pds.length; i++)
      if (pds[i].getName().equals(property))
        return isWritableProperty(pds[i]);
    return false;
  }

  public static Object getBeanProperty(Object bean, PropertyDescriptor pd)
  {
    Method getter = pd.getReadMethod();
    if (getter == null)
      return null;
    try {
      return getter.invoke(bean, new Object[]{});
    } catch (java.lang.IllegalAccessException e) {
      return null; //XXX throw exception instead?
    } catch (InvocationTargetException e) {
      return null; //XXX throw exception instead?
    }
    //XXX catch exceptions due to missing property, bad getter function,
    //    missing getter function,...
  }

  /**
   * Returns the value of a bean's property.
   * @param bean The bean to use.
   * @param property The name of the property to get.
   */
  public static Object getBeanProperty(Object bean, String property)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX throw exception instead?
      return null;
    };
    PropertyDescriptor[] pds = bi.getPropertyDescriptors();
    PropertyDescriptor pd = null;
    for (int i = 0; i < pds.length; i++) {
      if (pds[i].getName().equals(property)) {
        pd = pds[i];
        break;
      }
    }
    if (pd != null)
      return getBeanProperty(bean, pd);
    else
      return null;
    //XXX catch exceptions due to missing property, bad getter function,
    //    missing getter function,...
  }

  public static void setBeanProperty(Object bean, PropertyDescriptor pd,
      Object value)
  {
    Method setter = pd.getWriteMethod();
    try {
      setter.invoke(bean, new Object[]{value});
    } catch (IllegalAccessException e) {
      return; //XXX throw exception instead?
    } catch (java.lang.reflect.InvocationTargetException e) {
      return; //XXX throw exception instead?
    }
    //XXX catch exceptions due to missing property, bad setter function,
    //    missing setter function,...
  }

  /**
   * Sets the value of a bean's property.
   * @param bean The bean to use.
   * @param property The name of the property to set.
   * @param value The value to set the property to.
   */
  public static void setBeanProperty(Object bean, String property, Object value)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX throw exception instead?
      return;
    };
    PropertyDescriptor[] pds = bi.getPropertyDescriptors();
    PropertyDescriptor pd = null;
    for (int i = 0; i < pds.length; i++) {
      if (pds[i].getName().equals(property)) {
        pd = pds[i];
        break;
      }
    }
    setBeanProperty(bean, pd, value);
    //XXX catch exceptions due to missing property, bad setter function,
    //    missing setter function,...
  }

  /**
   * Returns true if <code>bean</code> can register the given type of
   * <code>listener</code>.
   * @param bean The bean to register with.
   * @param listener The type of listener to check <code>bean</code> for.
   */
  public static boolean providesEventSet(Object bean, Class<?> listener)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX throw exception instead?
      return false;
    };
    EventSetDescriptor[] esds = bi.getEventSetDescriptors();
    for (int i = 0; i < esds.length; i++)
      if (esds[i].getListenerType().equals(listener))
        return true;
    return false;
  }

  /**
   * Registers with <code>bean</code> a <code>listener</code> of a given type.
   * @param bean The bean to register with.
   * @param listenerType The type of listener to be registered with
   *        <code>bean</code>.
   * @param listener The listener to register with <code>bean</code>.
   * @return true if successful.
   */
  public static boolean addBeanListener(Object bean, Class<?> listenerType,
      Object listener)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX throw exception instead?
      return false;
    };
    EventSetDescriptor[] esds = bi.getEventSetDescriptors();
    EventSetDescriptor esd = null;
    for (int i = 0; i < esds.length; i++)
      if (esds[i].getListenerType().equals(listenerType)) {
        esd = esds[i];
        break;
      }
    if (esd == null)
      return false;
    Method adder = esd.getAddListenerMethod();
    try {
      adder.invoke(bean, new Object[]{listener});
    } catch (IllegalAccessException e) {
      return false; //XXX throw exception instead?
    } catch (InvocationTargetException e) {
      return false; //XXX throw exception instead?
    }
    return true;
  }

  /**
   * Unregisters with <code>bean</code> a <code>listener</code> of a given type.
   * @param bean The bean to unregister with.
   * @param listenerType The type of listener to be unregistered with
   *        <code>bean</code>.
   * @param listener The listener to unregister with <code>bean</code>.
   * @return true if successful.
   */
  public static boolean removeBeanListener(Object bean, Class<?> listenerType,
      Object listener)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e) {
      //XXX throw exception instead?
      return false;
    };
    EventSetDescriptor[] esds = bi.getEventSetDescriptors();
    EventSetDescriptor esd = null;
    for (int i = 0; i < esds.length; i++)
      if (esds[i].getListenerType().equals(listenerType)) {
        esd = esds[i];
        break;
      }
    if (esd == null)
      return false;
    Method remover = esd.getRemoveListenerMethod();
    try {
      remover.invoke(bean, new Object[]{listener});
    } catch (IllegalAccessException e) {
      return false; //XXX throw exception instead?
    } catch (InvocationTargetException e) {
      return false; //XXX throw exception instead?
    }
    return true;
  }

  public static EventListener[] getBeanListeners(Object bean, Class<?> listenerType)
  {
    BeanInfo bi;
    try {
      bi = Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException ex) {
      return new EventListener[]{};
    }
    EventSetDescriptor[] esds = bi.getEventSetDescriptors();
    EventSetDescriptor esd = null;
    for (int i = 0; i < esds.length; i++)
      if (esds[i].getListenerType().equals(listenerType)) {
        esd = esds[i];
        break;
      }
    if (esd == null)
      return new EventListener[]{};
    Method getter = esd.getGetListenerMethod();
    if (getter == null)
      return null;
    EventListener[] result;
    try {
      result = (EventListener[]) getter.invoke(bean, new Object[]{});
    } catch (IllegalAccessException ex) {
      return new EventListener[]{};
    } catch (InvocationTargetException ex) {
      return new EventListener[]{};
    }
    return result;
  }

  public static String translateClassName(String s)
  {
    if (s.charAt(0) == '[') {
      switch (s.charAt(1)) {
        case 'B' :
          return "byte[]";
        case 'C' :
          return "char[]";
        case 'D' :
          return "double[]";
        case 'F' :
          return "float[]";
        case 'I' :
          return "int[]";
        case 'J' :
          return "long[]";
        case 'L' :
          return s.substring(2, s.length() - 1) + "[]";
        case 'S' :
          return "short[]";
        case 'Z' :
          return "boolean[]";
        case 'V' :
          return "void[]";
        case '[' :
          return translateClassName(s.substring(1)) + "[]";
        default :
          throw new Error("Badly formatted Class name passed to "
              + "translateClassName:" + s);
      }
    }
    else {
      return s;
    }
  }

  public static String translateClassName(Class<?> c)
  {
    return translateClassName(c.getName());
  }

  public static void rememberBeanInfo(BeanInfo bi)
  {
    rememberedBeanInfos.add(bi);
  }

  public static void rememberBeanInfo(Class<?> type)
  {
    try {
      rememberBeanInfo(Introspector.getBeanInfo(type));
    } catch (IntrospectionException ex) {
    };
  }

  public static PropertyEditor getEditor(Class<?> clazz)
  {
    if (clazz == null)
      return null;
    if (editorCache.containsKey(clazz))
      return (PropertyEditor) editorCache.get(clazz);
    PropertyEditor result = PropertyEditorManager.findEditor(clazz);
    editorCache.put(clazz, result);
    return result;
  }
}
