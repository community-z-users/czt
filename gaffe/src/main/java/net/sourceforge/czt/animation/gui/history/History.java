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
import java.beans.beancontext.BeanContext;
import java.util.Map;

import net.sourceforge.czt.animation.ZLocator;
import net.sourceforge.czt.animation.gui.temp.SolutionSet;
import net.sourceforge.czt.animation.gui.temp.ZBinding;
import net.sourceforge.czt.animation.gui.temp.ZValue;

/**
 * Interface that all animation history objects derive from.
 */
public interface History
{
  /**
   * Getter for the name of the initialisation schema.
   */
  public String getInitSchema();

  /**
   * Setter for the name of the initialisation schema.
   */
  public void setInitSchema(String schemaName);

  /**
   * Getter for the name of the state schema.
   */
  public String getStateSchema();

  /**
   * Setter for the name of the state schema.
   */
  public void setStateSchema(String schemaName);

  /**
   * Returns the current solution set.
   * @return the current solution set, or null if the initialisation schema
   *         hasn't been set up yet.
   */
  public SolutionSet getCurrentSolutionSet();

  /**
   * Returns the current solution in the current solution set.
   * @return The current solution (or null if there's no solution).
   */
  public ZBinding getCurrentSolution();

  /**
   * Returns true if there is a current solution.
   * @return true if there is a current solution, false if there is no solution.
   */
  public boolean hasCurrentSolution();

  //Functions for activating schemas
  /**
   * Getter function for the map from locators, and the object.property to bind
   * them to.
   */
  public Map<ZLocator, ZValue> getInputs();

  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param value Value to bind variable to.
   */
  public void addInput(ZLocator variable, ZValue value);

  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param bean Java bean containing the property to set the variable to.
   * @param property Name of property in bean to set variable to.
   */
  public void addInput(ZLocator variable, Object bean, String property);

  /**
   * Convenience function for adding values into the inputs.
   * @param variable Location of variable to bind to value.
   * @param beanContext Context containing the bean to get the value from.
   * @param beanName Name of the java bean to get the value from.
   * @param property Name of property in bean to set variable to.
   */
  public void addInput(ZLocator variable, BeanContext beanContext,
                       String beanName, String property);

  /**
   * Performs an operation from the current solution.
   * First call to activateSchema must be to set the initialisation schema.
   * @param compositionText describes the operation to perform.
   * @throws ??? if first call wasn't an initialisation operation.
   * @throws ??? if ???
   */
  public void activateSchema(String schemaName);

  //Support for property change listeners on "currentSolution" and
  //"currentSolutionSet"
  /**
   * Function for adding property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public void addPropertyChangeListener(PropertyChangeListener listener);

  /**
   * Function for removing property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public void removePropertyChangeListener(PropertyChangeListener listener);

  /**
   * Getter function for property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public PropertyChangeListener[] getPropertyChangeListeners();

  /**
   * Function for adding property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public void addPropertyChangeListener(String propertyName,
      PropertyChangeListener listener);

  /**
   * Function for removing property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public void removePropertyChangeListener(String propertyName,
      PropertyChangeListener listener);

  /**
   * Getter function for property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public PropertyChangeListener[] getPropertyChangeListeners(String propertyName);

  /**
   * Check if a property has property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public boolean hasListeners(String propertyName);

  /**
   * Gives a label identifying the position in the history for use in GUI
   * display.
   */
  public String getPositionLabel();
};
