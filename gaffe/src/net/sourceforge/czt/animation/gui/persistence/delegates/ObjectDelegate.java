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

import java.beans.BeanInfo;
import java.beans.DefaultPersistenceDelegate;
import java.beans.Encoder;
import java.beans.Expression;
import java.beans.EventSetDescriptor;
import java.beans.IntrospectionException;
import java.beans.Introspector;
import java.beans.PersistenceDelegate;

import java.lang.reflect.Method;

import java.util.EventListener;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Vector;

import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

//Only extends DefaultPersistenceDelegate so that we can get at its protected members.
public class ObjectDelegate extends DefaultPersistenceDelegate {
  public ObjectDelegate() {};
  public ObjectDelegate(String[] consNames) {super(consNames);};

  public void writeObject(Object oldInstance, Encoder out) {
    Class type=oldInstance.getClass();
    BeanInfo bi;
    try {
      bi=Introspector.getBeanInfo(type);
    } catch (IntrospectionException ex) {
      return;
    };
    EventSetDescriptor[] esds=bi.getEventSetDescriptors();
    IdentityHashMap/*<Method,Vector<EventListener>>*/ removedListeners=new IdentityHashMap();

    synchronized(oldInstance) {
      for(int i=0;i<esds.length;i++) {
	Method getter=esds[i].getGetListenerMethod();
	Method remover=esds[i].getRemoveListenerMethod();
	Method adder=esds[i].getAddListenerMethod();
	if(removedListeners.get(adder)==null) removedListeners.put(adder,new Vector());
	EventListener[] listeners;
	try {
	  try {
	    listeners=(EventListener[]) getter.invoke(oldInstance,new Object[]{});
//    	    System.err.println("________ Successfully used get__Listeners() for "
//    			       +esds[i].getListenerType()+" from "+type);
	  } catch (Exception ex) {
//    	    System.err.println("________ Falling back on getListeners(Class) for "
//    			       +esds[i].getListenerType()+" from "+type);
	    getter=type.getMethod("getListeners",new Class[]{Class.class});
	    listeners=(EventListener[]) getter.invoke(oldInstance,new Object[]{esds[i].getListenerType()});
	  }
	  for(int j=0;j<listeners.length;j++) {
	    if(!listeners[j].getClass().getName().startsWith("net.sourceforge.czt.animation.gui")) continue;
	    remover.invoke(oldInstance,new Object[]{listeners[j]});
	    ((Vector)removedListeners.get(adder)).add(listeners[j]);
	  }
	} catch (Exception ex) {
//    	  System.err.println("________ Couldn't find listeners for "+esds[i].getListenerType()
//    			     +" from "+type);
//    	  System.err.println("________ Or Couldn't remove said listener");
//    	  ex.printStackTrace();
	}
      }

      super.writeObject(oldInstance,out);

      for(Iterator it=removedListeners.keySet().iterator();it.hasNext();) {
	Method adder=(Method)it.next();
	for(Iterator lIt=((Vector)removedListeners.get(adder)).iterator();lIt.hasNext();)
	  try {
	    adder.invoke(oldInstance,new Object[]{lIt.next()});
	  } catch (Exception ex) {
	    throw new Error("Could not re-add a listener that was removed to stop it being saved to the "
			    +"interface.",ex);
	  }
      };
    };
  };
};
