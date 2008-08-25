/**
 * The harness to run the gui
 */

package net.sourceforge.czt.modeljunit.gui;

import javax.swing.SwingUtilities;
import javax.swing.UIManager;

/*
 * Main.java
 * @author rong ID : 1005450 26th Jul 2007
 */

public class Main
{
  public static void main(String[] argv)
  {
    SwingUtilities.invokeLater(new Runnable()
    {
      public void run()
      {
        //Turn off metal's use of bold fonts
        UIManager.put("swing.boldMetal", Boolean.FALSE);
        ModelJUnitGUI gui = new ModelJUnitGUI();
        gui.createAndShowGUI();
      }
    });
  }
}
