
package net.sourceforge.czt.gaffe2.animation.model;

import javax.swing.tree.DefaultTreeModel;

/**
 * @author Linan Zhang
 *
 */
public class StepTree
{
  private static Step currentStep = new Step("Root",null);

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
    currentStep = step;
    step.firePropertyChange("index", -1, 0);
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
      currentStep = (Step) currentStep.getParent();
      currentStep.firePropertyChange("index", -1, 0);
      return true;
    }
    else {
      for (int i = 0; i < currentStep.getChildCount(); i++) {
        Step step = (Step) currentStep.getChildAt(i);
        if (step.getOperation().equals(operation)) {
          currentStep = step;
          currentStep.firePropertyChange("index", -1, 0);
          return true;
        }
      }
      return false;
    }
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
}
