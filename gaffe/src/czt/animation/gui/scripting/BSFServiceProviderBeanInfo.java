package czt.animation.gui.scripting;

import com.ibm.bsf.BSFManager;

import java.beans.Introspector;
import java.beans.IntrospectionException;

import java.beans.BeanInfo;
import java.beans.SimpleBeanInfo;

import java.beans.beancontext.BeanContextServiceProviderBeanInfo;

/**
 * <code>BeanInfo</code> for <code>BSFServiceProvider</code>.
 */
class BSFServiceProviderBeanInfo extends SimpleBeanInfo implements BeanContextServiceProviderBeanInfo {
  /**
   * Returns <code>BeanInfo</code>s for the services provided by <code>BSFServiceProvider</code>.
   */
  public BeanInfo[] getServicesBeanInfo() {
    try {
      return new BeanInfo[] {Introspector.getBeanInfo(BSFManager.class)};
    } catch (IntrospectionException e) {
      throw new Error("Could not get BeanInfo for BSFManager!:"+e);
    }
  };
};
