package net.sourceforge.czt.eclipse.zeves.core.internal;

import net.sourceforge.czt.eclipse.zeves.core.ZEves;

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
  
  private ZEves prover;

  @Override
  public void start(BundleContext context) throws Exception
  {
    super.start(context);
    plugin = this;
    
    prover = new ZEves();
  }

  @Override
  public void stop(BundleContext context) throws Exception
  {

    if (prover != null) {
      prover.stop();
      prover = null;
    }

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

  public static ZEves getZEves()
  {
    return getDefault().prover;
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
