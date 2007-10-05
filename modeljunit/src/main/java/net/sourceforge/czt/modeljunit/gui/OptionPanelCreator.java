
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