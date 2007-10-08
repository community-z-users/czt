
package net.sourceforge.czt.modeljunit.gui;
/**
 * AlgorithmPanel.java
 *
 * @author rong
 * ID : 1005450
 * 30th Jl 2007
 * */
public class OptionPanelCreator
{
  /** The number of algorithms plus a default panel.
   * 0. Default panel
   * 1. Random walk panel
   * 2. Greedy panel
  */ 
  public static final int NUM_PANE = 3;
  public static OptionPanelAdapter[] createPanels()
  {
    OptionPanelAdapter[] panes = new OptionPanelAdapter[NUM_PANE];
    panes[0] = new OptionPanelDefault(Parameter.ALGORITHM_NAME[0],
        "Select an algorithm from combobox.", "default.gif");
    panes[1] = new OptionPanelRandomWalking(Parameter.ALGORITHM_NAME[1],
        "Random algorithm to traverse the model", "random.gif");
    panes[2] = new OptionPanelGreedy(Parameter.ALGORITHM_NAME[2],
        "Greedy algorithm to traverse the model", "greedy.gif");
    return panes;
  }
  
  public static OptionPanelAdapter createOptionPane(String name, String explain, String imgPath)
  {
    if(name.equalsIgnoreCase(Parameter.ALGORITHM_NAME[0]))
      return new OptionPanelDefault(name, explain, imgPath);
    else if(name.equalsIgnoreCase(Parameter.ALGORITHM_NAME[1]))
      return new OptionPanelRandomWalking(name, explain, imgPath);
    else if(name.equalsIgnoreCase(Parameter.ALGORITHM_NAME[2]))
      return new OptionPanelGreedy(name, explain, imgPath);
    else
      return null;
  }

}