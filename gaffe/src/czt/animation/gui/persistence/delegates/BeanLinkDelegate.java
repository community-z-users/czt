package czt.animation.gui.persistence.delegates;

import czt.animation.gui.design.FormDesign;
import java.beans.BeanInfo;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.IntrospectionException;
import java.beans.Introspector;

public class BeanLinkDelegate extends DefaultPersistenceDelegate {
  private BeanLinkDelegate() {};
  private static final BeanLinkDelegate singleton=new BeanLinkDelegate();

  //Have to keep a strong reference to get around bug #4646747
  //Mentioned here:
  //http://java.sun.com/products/jfc/tsc/articles/persistence4/index.html
  private static final BeanInfo beanInfo;  
  static {
    try {
      beanInfo=Introspector.getBeanInfo(FormDesign.BeanLink.class);
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining BeanLink from "
		      +"BeanLinkDelegate."+ex);
    }
  };
  
  public static void registerDelegate() {
      beanInfo.getBeanDescriptor().setValue("persistenceDelegate", singleton);
  };
  protected boolean mutatesTo(Object oldInstance, Object newInstance) {
    return newInstance!=null;
  };
  protected Expression instantiate(Object oldInstance, Encoder out) {
    FormDesign.BeanLink oldLink=(FormDesign.BeanLink)oldInstance;
    System.err.println("@@B");
    return new Expression(oldLink,FormDesign.BeanLink.class,"new",
			  new Object[] {oldLink.source,
					oldLink.listener,
					oldLink.listenerType});
  };
};
