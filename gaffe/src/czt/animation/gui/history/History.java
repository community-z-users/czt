package czt.animation.gui.history;
import czt.animation.gui.temp.*;
import java.beans.*;
import java.util.Map;
import java.beans.beancontext.*;

/**
 * Interface that all animation history objects derive from.
 */
public interface History {

  /**
   * Returns the current solution set.
   * @return the current solution set, or null if the initialisation schema hasn't been set up yet.
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
   * Getter function for the map from locators, and the object.property to bind them to.
   * Map<ZLocator, ZValue>
   */
  public Map getInputs();

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
   * @param bean Name of the java bean to get the value from.
   * @param property Name of property in bean to set variable to.
   */
  public void addInput(ZLocator variable, BeanContext beanContext, String beanName, String property);
  
  /**
   * Performs an operation from the current solution.
   * First call to activateSchema must be to set the initialisation schema.
   * @param compositionText describes the operation to perform.
   * @throws ??? if first call wasn't an initialisation operation.
   * @throws ??? if ???
   */
  public void activateSchema(String schemaName);  



  //Support for property change listeners on "currentSolution" and "currentSolutionSet"
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
  public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener);
  /**
   * Function for removing property change listeners.
   * @see java.beans.PropertyChangeSupport
   */
  public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener);
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
};
