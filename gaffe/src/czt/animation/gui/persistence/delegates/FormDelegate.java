package czt.animation.gui.persistence.delegates;

import czt.animation.gui.Form;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.Statement;

import java.beans.beancontext.BeanContext;
import java.util.Iterator;

public class FormDelegate extends DefaultPersistenceDelegate {
  private FormDelegate() {};
  private static FormDelegate singleton=new FormDelegate();
  public static void registerDelegate() {
    try {
      Introspector.getBeanInfo(Form.class).getBeanDescriptor()
	.setValue("persistenceDelegate", singleton);
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining Form from "
		      +"FormDelegate."+ex);
    }
  };
  
  public void writeObject(Object oldInstance, Encoder out) {
    System.err.println("Started FormDelegate.writeObject(...)");
    super.writeObject(oldInstance,out);
    System.err.println("Ended FormDelegate.writeObject(...)");
  };
  protected boolean mutatesTo(Object oldInstance, Object newInstance) {
    System.err.println("Started FormDelegate.mutatesTo(...)");
    if(newInstance==null) {
      System.err.println("Ended FormDelegate.mutatesTo(...) = false");
      return false;
    }
    
    Form f=(Form)newInstance;
    BeanContext bc=(BeanContext)f.getBeanContextProxy();
    if(bc.size()==0) {
      System.err.println("Ended FormDelegate.mutatesTo(...) = true");
      return true;
    }
    System.err.println("Ended FormDelegate.mutatesTo(...) = false");
    System.err.println(" - "+bc.iterator().next());
    return false;
    
  };
  protected Expression instantiate(Object oldInstance, Encoder out) {
    System.err.println("Started FormDelegate.instantiate(...)");
    Expression e=super.instantiate(oldInstance,out);
    System.err.println("Ended FormDelegate.instantiate(...)");
    return e;
  };
  protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {    
    System.err.println("Started FormDelegate.initialize(...)");
    Form oldForm=(Form) oldInstance;
    Form newForm=(Form) newInstance;
    BeanContext oldBeanContext=(BeanContext) oldForm.getBeanContextProxy();
    BeanContext newBeanContext=(BeanContext) newForm.getBeanContextProxy();
    
    System.err.println("oldInstance = "+oldInstance);
    System.err.println("oldBeanContext.size = "+oldBeanContext.size());
    System.err.println("newInstance = "+newInstance);
    System.err.println("newBeanContext.size = "+newBeanContext.size());
    Form f=(Form)oldInstance;
    BeanContext bc=(BeanContext)f.getBeanContextProxy();
    for(Iterator i=bc.iterator();i.hasNext();) {
      System.err.println("Adding bean...");
      out.writeStatement(new Statement(oldInstance,"addBean",new Object[] {i.next()}));
    }
    super.initialize(type,oldInstance,newInstance,out);
    System.err.println("Ended FormDelegate.initialize(...)");
  };
};
