package net.sourceforge.czt.eclipse.core.internal;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 * 
 * @author Andrius Velykis
 */
public class CztCorePlugin extends Plugin
{

  // The plug-in ID
  public static final String PLUGIN_ID = "net.sourceforge.czt.eclipse.core"; //$NON-NLS-1$

  // The shared instance
  private static CztCorePlugin plugin;
  
  @Override
  public void start(BundleContext context) throws Exception
  {
    super.start(context);
    plugin = this;
  }

  @Override
  public void stop(BundleContext context) throws Exception
  {
    plugin = null;
    super.stop(context);
  }

  /**
   * Returns the shared instance
   * 
   * @return the shared instance
   */
  public static CztCorePlugin getDefault()
  {
    return plugin;
  }

  /**
   * Writes the message to the plug-in's log
   * 
   * @param message the text to write to the log
   */
  public static void log(String message, Throwable exception)
  {
    IStatus status = newErrorStatus(message, exception);
    getDefault().getLog().log(status);
  }

  public static void log(Throwable exception)
  {
    log(exception.getMessage(), exception);
  }

  /**
   * Returns a new <code>IStatus</code> for this plug-in
   */
  public static IStatus newErrorStatus(String message, Throwable exception)
  {
    if (message == null) {
      message = "";
    }
    return new Status(IStatus.ERROR, PLUGIN_ID, 0, message, exception);
  }

}
