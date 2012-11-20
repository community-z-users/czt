package net.sourceforge.czt.eclipse.zeves.core.internal;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 * 
 * @author Andrius Velykis
 */
public class ZEvesCorePlugin extends Plugin
{

  // The plug-in ID
  public static final String PLUGIN_ID = "net.sourceforge.czt.eclipse.zeves.core"; //$NON-NLS-1$

  // The shared instance
  private static ZEvesCorePlugin plugin;

  /*
   * (non-Javadoc)
   * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
   */
  @Override
  public void start(BundleContext context) throws Exception
  {
    super.start(context);
    plugin = this;
  }

  /*
   * (non-Javadoc)
   * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
   */
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
  public static ZEvesCorePlugin getDefault()
  {
    return plugin;
  }

  /**
   * Writes the message to the plug-in's log
   * 
   * @param message the text to write to the log
   */
  public void log(String message, Throwable exception)
  {
    IStatus status = newErrorStatus(message, exception);
    getLog().log(status);
  }

  public void log(Throwable exception)
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
