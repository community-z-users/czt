
package net.sourceforge.czt.modeljunit.gui;

import javax.swing.JOptionPane;

public class ErrorMessage
{

  public static void DisplayErrorMessage(String title, String msg)
  {
    Object[] options = {"OK"};
    JOptionPane.showOptionDialog(null, msg, title, JOptionPane.DEFAULT_OPTION,
        JOptionPane.ERROR_MESSAGE, null, options, options[0]);
  }

}
