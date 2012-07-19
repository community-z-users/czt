
package net.sourceforge.czt.animation.common.factory;

import net.sourceforge.czt.animation.view.MainFrame;
import net.sourceforge.czt.animation.view.OperationPane;
import net.sourceforge.czt.animation.view.StatusLabel;
import net.sourceforge.czt.animation.view.StepTreePane;
import net.sourceforge.czt.animation.view.ToolBar;
import net.sourceforge.czt.animation.view.VariablePane;

/**
 * @author Linan Zhang
 *
 */
public class GaffeUI
{
  private static MainFrame mainFrame;

  private static VariablePane statePane;

  private static VariablePane outputPane;

  private static VariablePane inputPane;

  private static StepTreePane stepTreePane;

  private static OperationPane operationPane;

  private static ToolBar toolBar;

  private static StatusLabel statusLabel;
  
  /**
   * No instance,solid
   */
  private GaffeUI()
  {
  }

  /**
   * @return Returns the mainFrame.
   */
  public static MainFrame getMainFrame()
  {
    return mainFrame;
  }

  /**
   * @return Returns the inputPane.
   */
  public static VariablePane getInputPane()
  {
    return inputPane;
  }

  /**
   * @return Returns the outputPane.
   */
  public static VariablePane getOutputPane()
  {
    return outputPane;
  }

  /**
   * @return Returns the statePane.
   */
  public static VariablePane getStatePane()
  {
    return statePane;
  }

  /**
   * @return Returns the currentPane.
   */
  public static StepTreePane getStepTreePane()
  {
    return stepTreePane;
  }

  /**
   * @return Returns the toolBar.
   */
  public static ToolBar getToolBar()
  {
    return toolBar;
  }

  /**
   * @return Returns the currentOperationPane.
   */
  public static OperationPane getOperationPane()
  {
    return operationPane;
  }

  /**
   * @return Returns the statusLabel.
   */
  public static StatusLabel getStatusLabel()
  {
    return statusLabel;
  }

  /**
   * reset all ui to original state
   */
  public static void resetAll()
  {
    if (statePane!=null) statePane.reset();
    if (outputPane!=null) outputPane.reset();
    if (operationPane!=null) operationPane.reset();
    if (toolBar!=null) toolBar.reset();
  }
  
  /**
   * @param inputPane The inputPane to set.
   */
  public static void setInputPane(VariablePane inputPane)
  {
    GaffeUI.inputPane = inputPane;
  }

  /**
   * @param mainFrame The mainFrame to set.
   */
  public static void setMainFrame(MainFrame mainFrame)
  {
    GaffeUI.mainFrame = mainFrame;
  }

  /**
   * @param operationPane The operationPane to set.
   */
  public static void setOperationPane(OperationPane operationPane)
  {
    GaffeUI.operationPane = operationPane;
  }

  /**
   * @param outputPane The outputPane to set.
   */
  public static void setOutputPane(VariablePane outputPane)
  {
    GaffeUI.outputPane = outputPane;
  }

  /**
   * @param statePane The statePane to set.
   */
  public static void setStatePane(VariablePane statePane)
  {
    GaffeUI.statePane = statePane;
  }

  /**
   * @param stepTreePane The stepTreePane to set.
   */
  public static void setStepTreePane(StepTreePane stepTreePane)
  {
    GaffeUI.stepTreePane = stepTreePane;
  }

  /**
   * @param toolBar The toolBar to set.
   */
  public static void setToolBar(ToolBar toolBar)
  {
    GaffeUI.toolBar = toolBar;
  }

  /**
   * @param statusLabel The statusLabel to set.
   */
  public static void setStatusLabel(StatusLabel statusLabel)
  {
    GaffeUI.statusLabel = statusLabel;
  }
}
