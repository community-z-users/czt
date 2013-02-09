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

package net.sourceforge.czt.animation.gui.history;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.beans.beancontext.BeanContext;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import net.sourceforge.czt.animation.ZLocator;
import net.sourceforge.czt.animation.gui.temp.SolutionSet;
import net.sourceforge.czt.animation.gui.temp.ZBinding;
import net.sourceforge.czt.animation.gui.temp.ZValue;
import net.sourceforge.czt.animation.gui.util.IntrospectionHelper;

/**
 * Basic History Interface that provides the traditional back/forward mechanism.
 */
public abstract class HistorySupport implements History
{
  protected String initSchema_ = null;

  protected String stateSchema_ = null;

  //XXX something should be done to protect against badly typed values
  //    being added.
  protected Map<ZLocator, ZValue> inputs_ = new HashMap<ZLocator, ZValue>();

  /**
   * Support class for property change listeners on <code>currentSolution</code>
   * and <code>currentSolutionSet</code>.
   */
  protected PropertyChangeSupport propertyChangeSupport;

  //Constructors
  /**
   * Basic constructor.
   * An initialisation schema must be set before the history can be used.
   * @see History#activateSchema(String)
   */
  public HistorySupport()
  {
    propertyChangeSupport = new PropertyChangeSupport(this);
  };

  /**
   * Sets the properties keeping track of state and initialisation schema names,
   * and activates the
   * initialisation schema.
   * @see History#activateSchema(String)
   * @param stateSchema The name of the state schema.
   * @param initSchema The name of the initialisation schema.
   */
  public HistorySupport(String stateSchema, String initSchema)
  {
    this();
    setStateSchema(stateSchema);
    setInitSchema(initSchema);
    activateSchema(initSchema);
  };

  public String getInitSchema()
  {
    return initSchema_;
  };

  public void setInitSchema(String schemaName)
  {
    initSchema_ = schemaName;
  };

  public String getStateSchema()
  {
    return stateSchema_;
  };

  public void setStateSchema(String schemaName)
  {
    stateSchema_ = schemaName;
  };

  //Functions from History
  public abstract SolutionSet getCurrentSolutionSet();

  public synchronized ZBinding getCurrentSolution()
  {
    SolutionSet currentSet = getCurrentSolutionSet();
    if (currentSet == null)
      return null;
    return currentSet.getCurrentSolution();
  };

  public synchronized boolean hasCurrentSolution()
  {
    SolutionSet currentSet = getCurrentSolutionSet();
    if (currentSet == null)
      return false;
    return currentSet.hasCurrentSolution();
  };

  //Functions for activating schemas
  /**
   * Getter function for the map from locators, and the object.property to bind
   * them to.
   */
  public Map<ZLocator, ZValue> getInputs()
  {
    return inputs_;
  };

  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param value Value to bind variable to.
   */
  public void addInput(ZLocator variable, ZValue value)
  {
    inputs_.put(variable, value);
  };

  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param bean Java bean containing the property to set the variable to.
   * @param property Name of property in bean to set variable to.
   */
  public void addInput(ZLocator variable, Object bean, String property)
  {
    ZValue value = (ZValue) IntrospectionHelper.getBeanProperty(bean, property);
    addInput(variable, value);
  };

  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param beanContext Context containing the bean to get the value from.
   * @param beanName Name of the java bean to get the value from.
   * @param property Name of property in bean to set variable to.
   */
  public void addInput(ZLocator variable, BeanContext beanContext,
                       String beanName, String property)
  {
    Iterator<?> i = beanContext.iterator();
    Object bean = null;
    while (i.hasNext()) {
      Object currBean;
      currBean = i.next();
      if (IntrospectionHelper.getBeanProperty(currBean, "name")
          .equals(beanName)) {
        bean = currBean;
        break;
      }
    };
    //XXX catch exceptions from reflection,introspection,missing bean
    addInput(variable, bean, property);
  };

  public synchronized void activateSchema(String schemaName)
  {
    //XXX does nothing at the moment.
    propertyChangeSupport.firePropertyChange("currentSolutionSet", null, null);
    propertyChangeSupport.firePropertyChange("currentSolution", null, null);
  };

  //Methods for navigating through the solutions
  /**
   * @return true if there is another solution in the current set after the
   *         current one.
   */
  public synchronized boolean hasNextSolution()
  {
    SolutionSet s = getCurrentSolutionSet();
    if (s == null)
      return false;
    else
      return s.hasNextSolution();
  }

  /**
   * Moves to the next solution in the current set.
   */
  public synchronized void nextSolution()
  {
    SolutionSet s = getCurrentSolutionSet();
    if (s != null) {
      s.nextSolution();
      //XXX would possibly be better to subscribe as listener on s, and forward
      //    those events received.
      propertyChangeSupport.firePropertyChange("currentSolution", null, null);
    }
  };

  /**
   * @return true if there is another solution in the current set before the
   *         current one.
   */
  public synchronized boolean hasPreviousSolution()
  {
    SolutionSet s = getCurrentSolutionSet();
    if (s == null)
      return false;
    else
      return s.hasPreviousSolution();
  };

  /**
   * Moves to the previous solution in the current set.
   */
  public synchronized void previousSolution()
  {
    SolutionSet s = getCurrentSolutionSet();
    if (s != null) {
      s.previousSolution();
      //XXX would possibly be better to subscribe as listener on s, and forward
      //    those events received.
      propertyChangeSupport.firePropertyChange("currentSolution", null, null);
    }
  };

  //Support for property change listeners on "currentSolution" and
  //"currentSolutionSet"
  public void addPropertyChangeListener(PropertyChangeListener listener)
  {
    propertyChangeSupport.addPropertyChangeListener(listener);
  };

  public void removePropertyChangeListener(PropertyChangeListener listener)
  {
    propertyChangeSupport.addPropertyChangeListener(listener);
  };

  public PropertyChangeListener[] getPropertyChangeListeners()
  {
    return propertyChangeSupport.getPropertyChangeListeners();
  };

  public void addPropertyChangeListener(String propertyName,
      PropertyChangeListener listener)
  {
    propertyChangeSupport.addPropertyChangeListener(propertyName, listener);
  };

  public void removePropertyChangeListener(String propertyName,
      PropertyChangeListener listener)
  {
    propertyChangeSupport.removePropertyChangeListener(propertyName, listener);
  };

  public PropertyChangeListener[] getPropertyChangeListeners(String propertyName)
  {
    return propertyChangeSupport.getPropertyChangeListeners(propertyName);
  };

  public boolean hasListeners(String propertyName)
  {
    return propertyChangeSupport.hasListeners(propertyName);
  };
};
