
package net.sourceforge.czt.animation.model;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;

import javax.swing.tree.DefaultTreeModel;

/**
 * @author Linan Zhang
 *
 */
@SuppressWarnings("serial")
public class StepTree extends DefaultTreeModel
{
  private String stateSchemaName;        // The state schema Name

  private String initSchemaName;         // The init  schema Name
 
  private Step step;                     // The current step

  private PropertyChangeSupport pcs;     // The bean property support, listens any property change and updates UI

  /**
   * Constructor with an empty root
   */
  public StepTree()
  {
    this(new Step("Root", null));
  }

  /**
   * Constructor with a given root
   * @param root
   */
  public StepTree(Step root)
  {
    super(root);
    stateSchemaName = "";
    initSchemaName = "";
    pcs = new PropertyChangeSupport(this);
    setStep(root);
  }

  /**
   * Add a new child step node to current step node
   * @param step
   */
  public void add(Step child)
  {
    step.add(child);
    setStep(child);
  }

  /**
   * Move to a specified child step node
   * @param
   */
  public boolean moveTo(String operation)
  {
    if (operation.equals("back")) {
      setStep((Step) step.getParent());
      return true;
    }
    else {
      for (int i = 0; i < step.getChildCount(); i++) {
        Step child = (Step) step.getChildAt(i);
        if (child.getOperation().equals(operation)) {
          setStep(child);
          return true;
        }
      }
      return false;
    }
  }

  /**
   * Change the current result index inside the current step node, acts as proxy to Step
   * @param index The index to set.
   */
  public boolean changeIndex(int newValue)
  {
    int oldValue = step.getIndex();
    boolean success = step.changeIndex(newValue);
    if (success) {
      firePropertyChange("index", oldValue, newValue);
    }
    return success;
  }

  /**
   * Get the available operations for the current step node. (The operations user has performed)
   * @return the available Operations
   */
  public String[] getAvailableOperations()
  {
    String[] result = new String[step.getChildCount()];
    for (int i = 0; i < step.getChildCount(); i++) {
      Step child = (Step) step.getChildAt(i);
      result[i] = child.getOperation();
    }
    return result;
  }

  /**
   * Whether this step have a parent step node
   * @return
   */
  public boolean hasPrevious()
  {
    return step.getLevel() > 0;
  }

  /**
   * Whether this step has a child step node
   * @return
   */
  public boolean hasNext()
  {
    return !step.isLeaf();
  }

  /**
   * Reset the root step node
   */
  public void reset()
  {
    setRoot(new Step("Root", null));
  }

  /**
   * return teh current selected step index;
   */
  public int getIndex()
  {
    return step.getIndex();
  }

  /**
   * return the current selected step size
   */
  public int size()
  {
    return step.size();
  }

  /**
   * @return whether the evalSet is completed
   */
  public boolean isComplete()
  {
    return step.isComplete();
  }

  /*--------------------------------------------------------------------------*/
  // Getter and Setters
  /**
   * @return Returns the stateSchemaName.
   */
  public String getStateSchemaName()
  {
    return stateSchemaName;
  }

  /**
   * @param stateSchemaName The stateSchemaName to set.
   */
  public void setStateSchemaName(String stateSchemaName)
  {
    this.stateSchemaName = stateSchemaName;
  }

  /**
   * @return Returns the initSchemaName.
   */
  public String getInitSchemaName()
  {
    return initSchemaName;
  }

  /**
   * @param initSchemaName The initSchemaName to set.
   */
  public void setInitSchemaName(String initSchemaName)
  {
    this.initSchemaName = initSchemaName;
  }

  /**
   * @return The selected Step
   */
  public Step getStep()
  {
    return step;
  }

  /**
   * @param currentStep The currentStep to set.
   */
  public void setStep(Step step)
  {
    this.step = step;
    firePropertyChange("step", -1, 0);
  }

  /*--------------------------------------------------------------------------*/

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeSupport#addPropertyChangeListener(java.beans.PropertyChangeListener)
   */
  public void addPropertyChangeListener(PropertyChangeListener arg0)
  {
    pcs.addPropertyChangeListener(arg0);
  }

  /* (non-Javadoc)
   * @see java.beans.PropertyChangeSupport#firePropertyChange(java.lang.String, int, int)
   */
  public void firePropertyChange(String arg0, int arg1, int arg2)
  {
    pcs.firePropertyChange(arg0, arg1, arg2);
  }

}
