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
package net.sourceforge.czt.animation.gui.persistence.delegates;

import java.awt.Component;
import java.awt.Container;

import java.beans.BeanInfo;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.Statement;

import java.beans.beancontext.BeanContext;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import javax.swing.JScrollPane;
import javax.swing.JViewport;

import net.sourceforge.czt.animation.gui.Form;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

public class FormDelegate extends DefaultPersistenceDelegate {
  private FormDelegate() {};
  private static FormDelegate singleton=new FormDelegate();
  public static void registerDelegate() {
    try {
      final BeanInfo beanInfo=Introspector.getBeanInfo(Form.class);
      IntrospectionHelper.rememberBeanInfo(beanInfo);
      beanInfo.getBeanDescriptor().setValue("persistenceDelegate", singleton);
    } catch (IntrospectionException ex) {
      throw new Error("Shouldn't get IntrospectionException examining Form from "
		      +"FormDelegate."+ex);
    }
  };
  
  public void writeObject(Object oldInstance, Encoder out) {
    super.writeObject(oldInstance,out);
  };
  protected boolean mutatesTo(Object oldInstance, Object newInstance) {
    if(newInstance==null) {
      return false;
    }
    
    Form f=(Form)newInstance;
    BeanContext bc=(BeanContext)f.getBeanContextProxy();
    if(bc.size()==0) {
      return true;
    }
    return false;
    
  };
  protected Expression instantiate(Object oldInstance, Encoder out) {
    Expression e=super.instantiate(oldInstance,out);
    return e;
  };
  protected void initialize(Class type, Object oldInstance, Object newInstance, Encoder out) {    
    Form oldForm=(Form) oldInstance;
    Form newForm=(Form) newInstance;
    BeanContext oldBeanContext=(BeanContext) oldForm.getBeanContextProxy();
    BeanContext newBeanContext=(BeanContext) newForm.getBeanContextProxy();

    //The location for the form bean should be transient, however location doesn't seem to appear as a
    //property for components, and XMLEncoder seems to ignore the transient property on x and y.
    //So we'll make it look like the location is the default, so it won't get stored.
    newForm.setLocation(oldForm.getLocation());

    //XXX There are similar problems with listeners.

    Form f=(Form)oldInstance;

    //This next step is done to make sure that component beans get added in the appropriate order.  So that
    //Containers with layouts don't end up with their child components rearranged.
    List bc=new Vector((BeanContext)f.getBeanContextProxy());
    List beans=makeSortedComponentList(f,bc,new Vector());
    beans.addAll(bc);

    for(Iterator i=beans.iterator();i.hasNext();) {
      Object obj=i.next();
      if(obj instanceof Component && ((Component)obj).getParent() !=f)
	if(((Component)obj).getParent() instanceof JViewport
	   &&((Component)obj).getParent().getParent() instanceof JScrollPane)
	  out.writeStatement(new Statement(oldInstance,"addBean",
					   new Object[] {obj, ((Component)obj).getParent().getParent()}));
	else
	  out.writeStatement(new Statement(oldInstance,"addBean",
					   new Object[] {obj, ((Component)obj).getParent()}));
      else
	out.writeStatement(new Statement(oldInstance,"addBean",
					 new Object[] {obj}));
    }
    
    super.initialize(type,oldInstance,newInstance,out);
  };
  /**
   * Used to sort the list of beans in a form based on the order they appear in their parents.
   * @param c the container whose children are recursively added to newList
   * @param bc only beans in this list are added to newList, after they are added to newList, they are
   *   removed from bc.
   * @param newList the list the beans are added to.
   * @return newList.
   */
  private static List makeSortedComponentList(Container c, List bc, List newList) {
    Component[] components=c.getComponents();
    for(int i=0;i<components.length;i++) if(!newList.contains(components[i])&&bc.contains(components[i])) {
      bc.remove(components[i]);
      newList.add(components[i]); 
      if(components[i] instanceof Container) makeSortedComponentList((Container)components[i],bc,newList);
    }
    return newList;
  };
  
};
