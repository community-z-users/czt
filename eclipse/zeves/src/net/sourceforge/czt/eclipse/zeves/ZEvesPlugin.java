package net.sourceforge.czt.eclipse.zeves;

import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.editor.ZEditorEditTracker;
import net.sourceforge.czt.eclipse.zeves.launch.ZEvesProcessSupport;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IStartup;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class ZEvesPlugin extends AbstractUIPlugin implements IStartup {

	// The plug-in ID
	public static final String PLUGIN_ID = "net.sourceforge.czt.eclipse.zeves"; //$NON-NLS-1$

	// The shared instance
	private static ZEvesPlugin plugin;
	
	private ZEves prover;
	private ZEditorEditTracker editTracker;
	private ZEvesProcessSupport proverProcessSupport;
	
	/**
	 * The constructor
	 */
	public ZEvesPlugin() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
		
		prover = new ZEves();
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
	public static ZEvesPlugin getDefault() {
		return plugin;
	}
	
	public static ZEves getZEves() {
		return getDefault().prover;
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
