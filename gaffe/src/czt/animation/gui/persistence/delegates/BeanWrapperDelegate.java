package czt.animation.gui.persistence.delegates;

import czt.animation.gui.design.BeanWrapper;

import java.awt.Component;

import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.Statement;

public class BeanWrapperDelegate extends DefaultPersistenceDelegate {
  private BeanWrapperDelegate() {};
  private static BeanWrapperDelegate singleton=new BeanWrapperDelegate();
  public static void registerDelegate() {
    try {
      Introspector.getBeanInfo(BeanWrapper.class).getBeanDescriptor()
	.setValue("persistenceDelegate",singleton);
      System.err.println("The changed persistenceDelegate is:"+Introspector.getBeanInfo(BeanWrapper.class).getBeanDescriptor().getValue("persistenceDelegate"));
      
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining BeanWrapper from "
		      +"BeanWrapperDelegate."+ex);
    }
  };
  public void writeObject(Object oldInstance, Encoder out) {
    super.writeObject(oldInstance,out);
  };
  protected boolean mutatesTo(Object oldInstance, Object newInstance) {
    return newInstance!=null;
  };
  protected Expression instantiate(Object oldInstance, Encoder out) {
    return super.instantiate(oldInstance,out);
  };
  protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {
    out.writeStatement(new Statement(oldInstance,"setBean",
				     new Object[] {((BeanWrapper)oldInstance).getBean()}));
    out.writeStatement(new Statement(oldInstance,"setBounds",
				     new Object[] {((Component)oldInstance).getBounds()}));
  };
};
