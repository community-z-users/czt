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
package czt.animation.gui.util;

import java.beans.BeanInfo;
import java.beans.EventSetDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PropertyDescriptor;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import java.util.EventListener;

/**
 * IntrospectionHelper provides functions for simplifying Introspection on beans in the rest of this
 * project.  Note this is a Singleton class - it can not be instantiated.
 * XXX needs work.
 */
public class IntrospectionHelper {
  /**
   * Private unused constructor to prevent creation of IntrospectionHelper objects.
   */
  private IntrospectionHelper() {};
  
  /**
   * Return true if a bean has a particular property.
   * @param bean The bean to check.
   * @param property The name of the property to check for.
   */
  static public boolean beanHasProperty(Object bean, String property) {
    BeanInfo bi;
    try {
      bi=Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e){
      //XXX ???
      return false;
    };
    
    PropertyDescriptor[] pds=bi.getPropertyDescriptors();
    PropertyDescriptor pd=null;
    for(int i=0;i<pds.length;i++) {
      if(pds[i].getName().equals(property)) {
	return true;
      }
    }
    return false;
  };
  
  /**
   * Return true if a bean has a particular property, and it is readable.
   * @param bean The bean to check.
   * @param property The name of the property to check for.
   */
  static public boolean beanHasReadableProperty(Object bean, String property) {
    BeanInfo bi;
    try {
      bi=Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e){
      //XXX ???
      return false;
    };
    PropertyDescriptor[] pds=bi.getPropertyDescriptors();
    PropertyDescriptor pd=null;
    for(int i=0;i<pds.length;i++) {
      if(pds[i].getName().equals(property)) {
	if(pds[i].getReadMethod()!=null)
	  return true;
	else 
	  return false;
      }
    }
    return false;
  };
  /**
   * Return true if a bean has a particular property, and it is writable.
   * @param bean The bean to check.
   * @param property The name of the property to check for.
   */
  static public boolean beanHasWritableProperty(Object bean, String property) {
    BeanInfo bi;
    try {
      bi=Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e){
      //XXX ???
      return false;
    };
    PropertyDescriptor[] pds=bi.getPropertyDescriptors();
    PropertyDescriptor pd=null;
    for(int i=0;i<pds.length;i++) {
      if(pds[i].getName().equals(property)) {
	if(pds[i].getWriteMethod()!=null) {
	  return true;
	} else {
	  return false;
	}
      }
    }
    return false;
  };

  /**
   * Returns the value of a bean's property.
   * @param bean The bean to use.
   * @param property The name of the property to get.
   */
  static public Object getBeanProperty(Object bean, String property) {
    BeanInfo bi;
    try {
      bi=Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e){
      //XXX throw exception instead?
      return null;
    };
    PropertyDescriptor[] pds=bi.getPropertyDescriptors();
    PropertyDescriptor pd=null;
    for(int i=0;i<pds.length;i++) {
      if(pds[i].getName().equals(property)) {
	pd=pds[i];
	break;
      }
    }
    Method getter=pd.getReadMethod();
    try {
      return getter.invoke(bean,new Object[]{});
    } catch (java.lang.IllegalAccessException e) {
      return null;//XXX throw exception instead?
    } catch (InvocationTargetException e) {
      return null;//XXX throw exception instead?
    }
    //XXX catch exceptions due to missing property, bad getter function, missing getter function,...
  };

  /**
   * Sets the value of a bean's property.
   * @param bean The bean to use.
   * @param property The name of the property to set.
   * @param value The value to set the property to.
   */
  static public void setBeanProperty(Object bean, String property, Object value) {
    BeanInfo bi;
    try {
      bi=Introspector.getBeanIn