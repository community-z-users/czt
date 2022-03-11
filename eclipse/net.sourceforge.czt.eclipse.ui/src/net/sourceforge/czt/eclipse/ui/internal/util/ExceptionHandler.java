/**
 * 
 */
package net.sourceforge.czt.eclipse.ui.internal.util;

import java.io.StringWriter;
import java.lang.reflect.InvocationTargetException;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;

/**
 * @author Chengdong Xu
 */
public class ExceptionHandler
{
  
  private static ExceptionHandler fgInstance= new ExceptionHandler();
  
  /**
     * Logs the given exception using the platform's logging mechanism. The exception is
     * logged as an error with the error code <code>JavaStatusConstants.INTERNAL_ERROR</code>.
     */
    public static void log(Throwable t, String message) {
        CztUIPlugin.log(new Status(IStatus.ERROR, CztUIPlugin.PLUGIN_ID, 
            1001, message, t));
    }
    
    /**
     * Handles the given <code>CoreException</code>. The workbench shell is used as a parent
     * for the dialog window.
     * 
     * @param e the <code>CoreException</code> to be handled
     * @param title the dialog window's window title
     * @param message message to be displayed by the dialog window
     */
    public static void handle(CoreException e, String title, String message) {
        handle(e, CztUIPlugin.getActiveWorkbenchShell(), title, message);
    }
    
    /**
     * Handles the given <code>CoreException</code>. 
     * 
     * @param e the <code>CoreException</code> to be handled
     * @param parent the dialog window's parent shell
     * @param title the dialog window's window title
     * @param message message to be displayed by the dialog window
     */
    public static void handle(CoreException e, Shell parent, String title, String message) {
        fgInstance.perform(e, parent, title, message);
    }
    
    /**
     * Handles the given <code>InvocationTargetException</code>. The workbench shell is used 
     * as a parent for the dialog window.
     * 
     * @param e the <code>InvocationTargetException</code> to be handled
     * @param title the dialog window's window title
     * @param message message to be displayed by the dialog window
     */
    public static void handle(InvocationTargetException e, String title, String message) {
        handle(e, CztUIPlugin.getActiveWorkbenchShell(), title, message);
    }
    
    /**
     * Handles the given <code>InvocationTargetException</code>. 
     * 
     * @param e the <code>InvocationTargetException</code> to be handled
     * @param parent the dialog window's parent shell
     * @param title the dialog window's window title
     * @param message message to be displayed by the dialog window
     */
    public static void handle(InvocationTargetException e, Shell parent, String title, String message) {
        fgInstance.perform(e, parent, title, message);
    }

    //---- Hooks for subclasses to control exception handling ------------------------------------
    
    protected void perform(CoreException e, Shell shell, String title, String message) {
        CztUIPlugin.log(e);
        IStatus status= e.getStatus();
        if (status != null) {
            ErrorDialog.openError(shell, title, message, status);
        } else {
            displayMessageDialog(e, e.getMessage(), shell, title, message);
        }
    }

    protected void perform(InvocationTargetException e, Shell shell, String title, String message) {
        Throwable target= e.getTargetException();
        if (target instanceof CoreException) {
            perform((CoreException)target, shell, title, message);
        } else {
            CztUIPlugin.log(e);
            if (e.getMessage() != null && e.getMessage().length() > 0) {
                displayMessageDialog(e, e.getMessage(), shell, title, message);
            } else {
                displayMessageDialog(e, target.getMessage(), shell, title, message);
            }
        }
    }

    //---- Helper methods -----------------------------------------------------------------------
    
    private void displayMessageDialog(Throwable t, String exceptionMessage, Shell shell, String title, String message) {
        StringWriter msg= new StringWriter();
        if (message != null) {
            msg.write(message);
            msg.write("\n\n"); //$NON-NLS-1$
        }
        if (exceptionMessage == null || exceptionMessage.length() == 0)
            msg.write("CZTUIMessages.ExceptionDialog_seeErrorLogMessage"); 
        else
            msg.write(exceptionMessage);
        MessageDialog.openError(shell, title, msg.toString());          
    }
}
