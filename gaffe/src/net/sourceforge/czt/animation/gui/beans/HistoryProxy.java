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
package net.sourceforge.czt.animation.gui.beans;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeSupport;
import java.beans.PropertyVetoException;

import java.beans.beancontext.BeanContext;
import java.beans.beancontext.BeanContextChildSupport;
import java.beans.beancontext.BeanContextServiceAvailableEvent;
import java.beans.beancontext.BeanContextServiceRevokedEvent;
import java.beans.beancontext.BeanContextServices;

import java.util.TooManyListenersException;

import net.sourceforge.czt.animation.gui.history.History;

import net.sourceforge.czt.animation.gui.temp.*;

public class HistoryProxy extends BeanContextChildSupport {
  private History history=null;

  public SolutionSet getCurrentSolutionSet() {return history.getCurrentSolutionSet();};
  public ZBinding getCurrentSolution() {return history.getCurrentSolution();};
  public boolean hasCurrentSolution() {return history!=null && history.hasCurrentSolution();};


  //Support for property change listeners on "currentSolution" and "currentSolutionSet"
  private final PropertyChangeSupport propertyChangeSupport=new PropertyChangeSupport(this);
  
  public void addPropertyChangeListener(PropertyChangeListener listener) {
    propertyChangeSupport.addPropertyChangeListener(listener);
  };
  public void removePropertyChangeListener(PropertyChangeListener listener) {
    propertyChangeSupport.removePropertyChangeListener(listener);    
  };
  public PropertyChangeListener[] getPropertyChangeListeners() {
    return propertyChangeSupport.getPropertyChangeListeners();
  };
  public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
    propertyChangeSupport.addPropertyChangeListener(propertyName,listener);
  };
  public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
    propertyChangeSupport.removePropertyChangeListener(propertyName,listener);
  };
  public PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
    return propertyChangeSupport.getPropertyChangeListeners(propertyName);
  };
  public boolean hasListeners(String propertyName) {
    return propertyChangeSupport.hasListeners(propertyName);
  };

  private final PropertyChangeListener pcListener=new PropertyChangeListener() {
      public void propertyChange(PropertyChangeEvent evt) {
	propertyChangeSupport
	  .firePropertyChange(new PropertyChangeEvent(HistoryProxy.this, evt.getPropertyName(),
						      evt.getOldValue(), evt.getNewValue()));
      };
    };

  public void serviceAvailable(BeanContextServiceAvailableEvent bcsae) {
    if(bcsae.getServiceClass().equals(History.class)) {
      try {
	history=(History)((BeanContextServices)getBeanContext())
	  .getService(this,this,History.class,null,this);
	history.addPropertyChangeListener("currentSolution",pcListener);
	history.addPropertyChangeListener("currentSolutionSet",pcListener);
      } catch (TooManyListenersException ex) {}
    }
  };
  public void serviceRevoked(BeanContextServiceRevokedEvent bcsre) {
    if(bcsre.getServiceClass().equals(History.class)) {
      history.removePropertyChangeListener("currentSolution",pcListener);
      history.removePropertyChangeListener("currentSolutionSet",pcListener);
      history=null;
    };
  };
  public void setBeanContext(BeanContext bc) throws PropertyVetoException {
    BeanContext oldBC=getBeanContext();
    super.setBeanContext(bc);
    if(oldBC!=null && oldBC instanceof BeanContextServices)
      ((BeanContextServices)oldBC).removeBeanContextServicesListener(this);
    if(bc!=null && bc instanceof BeanContextServices)
      ((BeanContextServices)bc).addBeanContextServicesListener(this);
  };  
};
