
package net.sourceforge.czt.modeljunit.gui;

/*
 * AlgorithmPanel.java
 * @author rong ID : 1005450 30th Jul 2007
 */
public class OptionPanelCreator
{
  /** The number of algorithms plus a default panel.
   * 0. Random walk panel
   * 1. Greedy panel
   * 2. Lookahead tester panel
  */
  public static final int NUM_PANE = 3;

  public static final String[] ALGORITHM_NAME = {"Random", "Greedy",
      "Lookahead"};

  public static OptionPanelAdapter[] createPanels()
  {
    OptionPanelAdapter[] panes = new OptionPanelAdapter[NUM_PANE];
    panes[0] = new OptionPanelRandomWalking(ALGORITHM_NAME[0],
        "Random algorithm to traverse the model", "random.gif");
    panes[1] = new OptionPanelGreedy(ALGORITHM_NAME[1],
        "Greedy algorithm to traverse the model", "greedy.gif");
    panes[2] = new OptionPanelLookahead(ALGORITHM_NAME[2],
        "Lookahead algorithm looks several levels ahead to find "
            + "unexplored transitions", "lookahead.gif");
    return panes;
  }
}
