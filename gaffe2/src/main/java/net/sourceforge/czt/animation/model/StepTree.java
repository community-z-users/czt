
package net.sourceforge.czt.animation.model;

import javax.swing.tree.DefaultTreeModel;

/**
 * @author Linan Zhang
 *
 */
public class StepTree
{
  private static String stateSchemaName = "";

  private static String initSchemaName = "";

  private static Step currentStep = new Step("Root", null);

  private static DefaultTreeModel stepTree = new DefaultTreeModel(currentStep);

  /**
   * 
   */
  private StepTree()
  {
  }

  /**
   * @param step
   */
  public static void add(Step step)
  {
    currentStep.add(step);
    setCurrentStep(step);
  }

  /**
   * @return The selected Step
   */
  public static Step getCurrentStep()
  {
    return currentStep;
  }

  /**
   * @param currentStep The currentStep to set.
   */
  public static void setCurrentStep(Step currentStep)
  {
    StepTree.currentStep = currentStep;
    currentStep.firePropertyChange("index", -1, 0);
  }

  /**
   * @return the available Operations
   */
  public static String[] getAvailableOperations()
  {
    String[] result = new String[currentStep.getChildCount()];
    for (int i = 0; i < currentStep.getChildCount(); i++) {
      Step step = (Step) currentStep.getChildAt(i);
      result[i] = step.getOperation();
    }
    return result;
  }

  /**
   * @param index The index to set.
   */
  public static boolean moveTo(String operation)
  {
    if (operation.equals("back")) {
      setCurrentStep((Step) currentStep.getParent());
      return true;
    }
    else {
      for (int i = 0; i < currentStep.getChildCount(); i++) {
        Step step = (Step) currentStep.getChildAt(i);
        if (step.getOperation().equals(operation)) {
          setCurrentStep(step);
          return true;
        }
      }
      return false;
    }
  }

  /**
   * 
   */
  public static void reset()
  {
    currentStep = new Step("Root", null);
    stepTree = new DefaultTreeModel(currentStep);
  }

  /**
   * @return
   */
  public static boolean hasPrevious()
  {
    return currentStep.getLevel() > 1;
  }

  /**
   * @return
   */
  public static boolean hasNext()
  {
    return !currentStep.isLeaf();
  }

  /**
   * @return Returns the stepTree.
   */
  public static DefaultTreeModel getStepTree()
  {
    return stepTree;
  }

  /**
   * @param stepTree The stepTree to set.
   */
  public static void setStepTree(DefaultTreeModel stepTree)
  {
    StepTree.stepTree = stepTree;
  }

  /**
   * @return Returns the initSchemaName.
   */
  public static String getInitSchemaName()
  {
    return initSchemaName;
  }

  /**
   * @param initSchemaName The initSchemaName to set.
   */
  public static void setInitSchemaName(String initSchemaName)
  {
    StepTree.initSchemaName = initSchemaName;
  }

  /**
   * @return Returns the stateSchemaName.
   */
  public static String getStateSchemaName()
  {
    return stateSchemaName;
  }

  /**
   * @param stateSchemaName The stateSchemaName to set.
   */
  public static void setStateSchemaName(String stateSchemaName)
  {
    StepTree.stateSchemaName = stateSchemaName;
  }

}
