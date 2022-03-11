
package net.sourceforge.czt.eclipse.ui.internal.util;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleConstants;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.IConsoleView;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

/**
 * @author Chengdong Xu
 */
public class CZTConsoleUtility
{

  private static final String DEFAULT_CONSOLE_NAME = "CZT";

  /**
   * Prints out the given message represented by a string buffer to an Eclipse console with a default name - CZT
   * @param message a message to print out
   */
  public static void outputToConsole(String message)
  {
    MessageConsole console = findConsole(DEFAULT_CONSOLE_NAME);
    outputToConsole(message, console);
  }

  /**
   * Prints out the given message represented by a string buffer to an Eclipse console with the given name
   * @param message the message to print out
   * @param consoleName the name of the console for print
   */
  public static void outputToConsole(String message, String consoleName)
  {
    MessageConsole console = findConsole(consoleName);
    outputToConsole(message, console);
  }

  /**
   * Prints out the given message represented by a string buffer to the given Eclipse console
   * @param message the message to print out
   * @param console the console for print
   */
  public static void outputToConsole(String message, MessageConsole console)
  {
    try {
      /*
       * Reveal the Console view
       * and ask it to display a particular console instance
       */
      IWorkbenchPage page = PlatformUI.getWorkbench()
          .getActiveWorkbenchWindow().getActivePage();
      if (page == null)
        return;
      String id = IConsoleConstants.ID_CONSOLE_VIEW;
      IConsoleView view = (IConsoleView) page.showView(id);
      view.display(console);

      MessageConsoleStream out = console.newMessageStream();
      out.println(message);
    } catch (PartInitException e) {
      CztUIPlugin
          .getDefault()
          .getLog()
          .log(
              new Status(
                  IStatus.ERROR,
                  CztUIPlugin.PLUGIN_ID,
                  0,
                  "Error occurred opening console",
                  e));
    }
  }

  /**
   * Find an existing console or create a new console if not found
   * @param name the name of the console
   * @return an existing console or a new console if not found
   */
  public static MessageConsole findConsole(String name)
  {
    ConsolePlugin conPlugin = ConsolePlugin.getDefault();
    IConsoleManager conManager = conPlugin.getConsoleManager();
    IConsole[] existing = conManager.getConsoles();
    for (int i = 0; i < existing.length; i++)
      if (name.equals(existing[i].getName()))
        return (MessageConsole) existing[i];
    //No console found, so create a new one
    MessageConsole newConsole = new MessageConsole(name, null);
    conManager.addConsoles(new IConsole[]{newConsole});

    return newConsole;
  }
}
