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
package czt.animation.gui.history;

import czt.animation.gui.temp.*;
import czt.animation.gui.util.IntrospectionHelper;

import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Vector;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

import java.beans.beancontext.BeanContext;

/**
 * Basic History Interface that provides the traditional back/forward mechanism.
 */
public abstract class HistorySupport implements History {
  

  //Constructors
  /**
   * Basic constructor.
   * An initialisation schema must be set before the history can be used.
   * @see czt.animation.gui.history.History#activateSchema(String)
   */
  public HistorySupport() {
    propertyChangeSupport=new PropertyChangeSupport(this);
  };


  //Functions from History
  public abstract SolutionSet getCurrentSolutionSet();
  public synchronized ZBinding getCurrentSolution() {
    SolutionSet currentSet=getCurrentSolutionSet();
    if(currentSet==null) return null;
    return currentSet.getCurrentSolution();
  };
  public synchronized boolean hasCurrentSolution() {
    SolutionSet currentSet=getCurrentSolutionSet();
    if(currentSet==null) return false;
    return currentSet.hasCurrentSolution();
  };

  //Functions for activating schemas
  protected Map inputs;//XXX something should be done to protect against badly typed values being 
                       //added.
  /**
   * Getter function for the map from locators, and the object.property to bind them to.
   * Map<ZLocator, ZValue>
   */
  public Map getInputs() {return inputs;};
  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param value Value to bind variable to.
   */
  public void addInput(ZLocator variable, ZValue value) {
    inputs.put(variable,value);
  };
  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param bean Java bean containing the property to set the variable to.
   * @param property Name of property in bean to set variable to.
   */
  public void addInput(ZLocator variable, Object bean, String property) {
    addInput(variable,(ZValue)IntrospectionHelper.getBeanProperty(bean,property));
  };
  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param beanContext Context containing the bean to get the value from.
   * @param bean Name of the java bean to get the value from.
   * @param property Name of property in bean to set variable to.
   */
  public void addInput(ZLocator variable, BeanContext beanContext, String beanName, String property) {
    Iterator i=beanContext.iterator();
    Object bean=null;
    while(i.hasNext()) {
      Object currBean;
      currBean=i.next();
      if(IntrospectionHelper.getBeanProperty(currBean,"name").equals(beanName)) {
	bean=currBean;
	break;
      }
    };
    //XXX catch exceptions from reflection,introspection,missing bean
    addInput(variable,bean,property);
  };

  public synchronized void activateSchema(String schemaName) {
    //XXX does nothing at the moment.
    propertyChangeSupport.firePropertyChange("currentSolutionSet",null,null);
    propertyChangeSupport.firePropertyChange("currentSolution",null,null);
  };


  //Methods for navigating through the solutions
   /**
   * @return true if there is another solution in the current set after the current one.
   */
  public synchronized boolean hasNextSolution() {
    SolutionSet s=getCurrentSolutionSet();
    return (s==null)?false:s.hasNextSolution();
  }
  /**
   * Moves to the next solution in the current set.
   */
  public synchronized void nextSolution() {
    SolutionSet s=getCurrentSolutionSet();
    if(s!=null) {
      s.nextSolution();
      //XXX would possibly be better to subscribe as listener on s, and forward those events received.
      propertyChangeSupport.firePropertyChange("currentSolution",null,null);
    }
  };
  /**
   * @return true if there is another solution in the current set before the current one.
   */
  public synchronized boolean hasPreviousSolution() {
    SolutionSet s=getCurrentSolutionSet();
    return (s==null)?false:s.hasPreviousSolution();
  };
  /**
   * Moves to the previous solution in the current set.
   */
  public synchronized void previousSolution() {
    SolutionSet s=getCurrentSolutionSet();
    if(s!=null) {
      s.previousSolution();
      //XXX would possibly be better to subscribe as listener on s, and forward those events received.
      propertyChangeSupport.firePropertyChange("currentSolution",null,null);
    }
  };


  //Support for property change listeners on "currentSolution" and "currentSolutionSet"
  /**
   * Support class for property change listeners on <code>currentSolution</code> and 
   * <code>currentSolutionSet</code>.
   */
  protected PropertyChangeSupport propertyChangeSupport;
  
  public void addPropertyChangeListener(PropertyChangeListener listener) {
    propertyChangeSupport.addPropertyChangeListener(listener);
  };
  public void removePropertyChangeListener(PropertyChangeListener listener) {
    propertyChangeSupport.addPropertyChangeListener(listener);
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
};

