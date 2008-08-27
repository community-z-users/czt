
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

  public static final String[] ALGORITHM_NAME = {
    "Random Walk",
    "Greedy Walk",
    "Lookahead Walk"
    };

  public static OptionPanelAdapter[] createPanels()
  {
    OptionPanelAdapter[] panes = new OptionPanelAdapter[NUM_PANE];
    panes[0] = new OptionPanelRandomWalk(ALGORITHM_NAME[0],
        "The Random Walk walk algorithm chooses any enabled "
        +"transition at each step",
        "random.gif");
    panes[1] = new OptionPanelGreedy(ALGORITHM_NAME[1],
        "The Greedy Walk algorithm gives preference to unexplored "
        +"transitions.  It chooses randomly if all have been explored",
        "greedy.gif");
    panes[2] = new OptionPanelLookahead(ALGORITHM_NAME[2],
        "The Lookahead Walk algorithm looks ahead 'Depth' levels to find "
        + "unexplored transitions",
        "lookahead.gif");
    return panes;
  }
}
