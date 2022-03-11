package net.sourceforge.czt.eclipse.zeves.ui;

import net.sourceforge.czt.eclipse.zeves.ui.editor.ZEditorEditTracker;
import net.sourceforge.czt.eclipse.zeves.ui.launch.ZEvesProcessSupport;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IStartup;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class ZEvesUIPlugin extends AbstractUIPlugin implements IStartup {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sourceforge.czt.eclipse.zeves.ui"; //$NON-NLS-1$

	// The shared instance
	private static ZEvesUIPlugin plugin;
	
	private ZEditorEditTracker editTracker;
	private ZEvesProcessSupport proverProcessSupport;
	
	/**
	 * The constructor
	 */
	public ZEvesUIPlugin() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		
		proverProcessSupport = new ZEvesProcessSupport();
		editTracker = new ZEditorEditTracker();
		editTracker.init();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {

		if (editTracker != null) {
			editTracker.dispose();
			editTracker = null;
		}
		
		if (proverProcessSupport != null) {
			proverProcessSupport.dispose();
			proverProcessSupport = null;
		}
		
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static ZEvesUIPlugin getDefault() {
		return plugin;
	}
	
	public static ZEvesProcessSupport getZEvesProcessSupport() {
		return getDefault().proverProcessSupport;
	}
	
	/**
	 * Writes the message to the plug-in's log
	 * 
	 * @param message the text to write to the log
	 */
	public void log(String message, Throwable exception) {
		IStatus status = newErrorStatus(message, exception);
		getLog().log(status);
	}
	
	public void log(ZEvesException ex) {

		String msg = ex.getMessage();
		
		String debugInfo = ex.getDebugInfo();
		if (debugInfo != null) {
			msg = msg + "\n\n" + debugInfo;
		}
		
		log(msg, ex);
	}
	
	public void log(Throwable exception) {
		log(exception.getMessage(), exception);
	}
	
	/**
	 * Returns a new <code>IStatus</code> for this plug-in
	 */
	public static IStatus newErrorStatus(String message, Throwable exception) {
		if (message == null) {
			message = ""; 
		}		
		return new Status(IStatus.ERROR, PLUGIN_ID, 0, message, exception);
	}

	@Override
	public void earlyStartup() {
		getDefault();
	}

}
