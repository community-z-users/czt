/**
 * @author rong The purpose is the class is display an error dialog with error
 *         message to users.
 */

package net.sourceforge.czt.modeljunit.gui;

import javax.swing.JOptionPane;

/*
 * ErrorMessage.java
 * @author rong ID : 1005450 26th Jul 2007
 */
public class ErrorMessage
{

  public static void DisplayErrorMessage(String title, String msg)
  {
    Object[] options = {"OK"};
    JOptionPane.showOptionDialog(null, msg, title, JOptionPane.DEFAULT_OPTION,
        JOptionPane.ERROR_MESSAGE, null, options, options[0]);
  }

}
