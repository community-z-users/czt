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

import net.sourceforge.czt.animation.gui.Form;
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
    BeanContext bc=(BeanContext)f.getBeanContextProxy();
    for(Iterator i=bc.iterator();i.hasNext();) {
      out.writeStatement(new Statement(oldInstance,"addBean",new Object[] {i.next()}));
    }
    
    super.initialize(type,oldInstance,newInstance,out);
  };
};
