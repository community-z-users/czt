
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
  private String stateSchemaName;

  private String initSchemaName;

  private Step step;

  private PropertyChangeSupport pcs;

  /**
   * constructor
   */
  public StepTree()
  {
    this(new Step("Root", null));
  }

  public StepTree(Step root)
  {
    super(root);
    stateSchemaName = "";
    initSchemaName = "";
    pcs = new PropertyChangeSupport(this);
  }

  /**
   * @param step
   */
  public void add(Step child)
  {
    step.add(child);
    setStep(child);
  }

  /**
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
   * @return
   */
  public boolean hasPrevious()
  {
    return step.getLevel() > 1;
  }

  /**
   * @return
   */
  public boolean hasNext()
  {
    return !step.isLeaf();
  }

  /**
   * 
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
   * @return
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
