package czt.animation.gui.util;
import java.beans.*;
import java.lang.reflect.*;

/**
 * IntrospectionHelper provides functions for simplifying Introspection on beans in the rest of this
 * project.
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
    } catch (java.lang.reflect.InvocationTargetException e) {
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
      bi=Introspector.getBeanInfo(bean.getClass());
    } catch (IntrospectionException e){
      //XXX throw exception instead?
      return;
    };
    PropertyDescriptor[] pds=bi.getPropertyDescriptors();
    PropertyDescriptor pd=null;
    for(int i=0;i<pds.length;i++) {
      if(pds[i].getName().equals(property)) {
	pd=pds[i];
	break;
      }
    }
    Method setter=pd.getWriteMethod();
    try {
      setter.invoke(bean,new Object[]{value});
    } catch (java.lang.IllegalAccessException e) {
      return;//XXX throw exception instead?
    } catch (java.lang.reflect.InvocationTargetException e) {
      return;//XXX throw exception instead?
    }
    //XXX catch exceptions due to missing property, bad setter function, missing setter function,...
  };
};






