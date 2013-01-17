package net.sourceforge.czt.eclipse.zeves.ui.launch;

import java.io.IOException;
import java.net.ConnectException;

import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.zeves.ZEvesApi;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.PlatformUI;

public abstract class ZEvesRemoteLaunch extends LaunchConfigurationDelegate {

	private static final int DEFAULT_PORT = 6789;
	private static final int RETRY_MAX = 30;
	
	@Override
	public void launch(ILaunchConfiguration configuration, String mode, ILaunch launch, IProgressMonitor monitor)
			throws CoreException {
		
		if (monitor.isCanceled()) {
			return;
		}
		
		ZEves prover = ZEvesCore.getZEves();
		if (prover.isLaunched()) {
        	// we only allow one prover instance
        	abort("Only a single Z/EVES prover can be running at any time - stop the running prover before launching a new one");
        	return;
        }
		
		// flag to avoid concurrent launches
		prover.setStarting(true);
		try {
			doLaunch(configuration, mode, launch, monitor, prover);
		} finally {
			prover.setStarting(false);
		}
	}

	private void doLaunch(ILaunchConfiguration configuration, String mode, ILaunch launch, IProgressMonitor monitor,
			ZEves prover) throws CoreException {
		if (monitor.isCanceled()) {
			return;
		}

		String address = getServerAddress(configuration);

		if (monitor.isCanceled()) {
			return;
		}
		
		int port = getPortConfig(configuration);

		if (monitor.isCanceled()) {
			return;
		}
		
		if (monitor.isCanceled()) {
			return;
		}
		
		startProver(configuration, mode, launch, monitor, prover, address, port);
	}
	
	protected void startProver(ILaunchConfiguration configuration, String mode, ILaunch launch,
			IProgressMonitor monitor, ZEves prover, String address, int port) throws CoreException {
		
		monitor.beginTask("Launching " + configuration.getName() + "...", IProgressMonitor.UNKNOWN);
		
		startProver(prover, address, port, monitor);
		
		System.out.println("Done launching");
	}
	
	protected boolean startProver(ZEves prover, String serverAddress, int port, IProgressMonitor monitor)
			throws CoreException {
		
		if (monitor.isCanceled()) {
			return false;
		}
		
		ZEvesApi api = new ZEvesApi(serverAddress, port);

		if (!api.isConnected()) {
			try {
				while (!connectRetry(api, monitor)) {
					// cannot connect
					if (!askToRetry()) {
						return false;
					}
				}
			} catch (IOException e) {
				abort("Problems connecting to Z/EVES server: " + e.getMessage(), e, 0);
				return false;
			}
		}
		
		if (api.isConnected()) {
			prover.setApi(api);
		}
		
		return true;
	}
	
	private boolean askToRetry() {
		
		// raise a dialog in the UI thread
		final int[] result = new int[1];
		PlatformUtil.runInUI(true, new Runnable() {
			
			@Override
			public void run() {
				Shell shell = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getShell();
				MessageDialog dialog = new MessageDialog(shell, "Retry", null, "Cannot connect to Z/EVES server, retry?",
						MessageDialog.QUESTION, new String[] {"Retry", "Cancel"}, 0) {

							@Override
							public int open() {
								setShellStyle(getShellStyle() | SWT.SHEET);
								return super.open();
							}
				};
				
				result[0] = dialog.open();
			}
		});
		
		return result[0] == 0;
	}
	
	private boolean connectRetry(ZEvesApi api, IProgressMonitor monitor) throws IOException {
		
		int tries = 0;
		while (tries < RETRY_MAX) {
			try {
				api.connect();
			} catch (ConnectException e) {
				
				if (monitor.isCanceled()) {
					// stop connecting
					return true;
				}
				
				// cannot connect (socket not yet available), retry after 1 second
				try {
					Thread.sleep(1000);
				} catch (InterruptedException e1) {}
				
				if (monitor.isCanceled()) {
					// stop connecting
					return true;
				}
				
				tries++;
				continue;
			}
			
			// connected successfully
			return true;
		}
		
		return false;
	}
	
    protected String getServerAddress(ILaunchConfiguration configuration) throws CoreException {
    	
    	String address = getServerAddressConfig(configuration);
    	
    	if (address == null || address.isEmpty()) {
			abort("Z/EVES server address is not specified");
		}
    	
    	return address;
    }
    
    public static String getServerAddressConfig(ILaunchConfiguration configuration) {
    	String address = ""; //$NON-NLS-1$
		try {
			address = configuration.getAttribute(ZEvesLaunchConstants.ATTR_SERVER_ADDR, ""); //$NON-NLS-1$; 
		} catch (CoreException ce) {
			ZEvesUIPlugin.getDefault().log("Error reading configuration", ce);
		}
		return address;
	}
    
    public static int getPortConfig(ILaunchConfiguration configuration) {
		int port= DEFAULT_PORT;
		try {
			port= configuration.getAttribute(ZEvesLaunchConstants.ATTR_PORT, DEFAULT_PORT); 
		} catch (CoreException ce) {
			ZEvesUIPlugin.getDefault().log("Error reading configuration", ce);
		}
		return port;
	}
    
	/**
	 * Throws a core exception with an error status object built from
	 * the given message, lower level exception, and error code.
	 * @param message the status message
	 * @param exception lower level exception associated with the
	 *  error, or <code>null</code> if none
	 * @param code error code
	 */
	protected static void abort(String message, Throwable exception, int code) throws CoreException {
		throw new CoreException(new Status(IStatus.ERROR, ZEvesUIPlugin.PLUGIN_ID, code, message, exception));
	}
	
	protected static void abort(String message) throws CoreException {
		abort(message, null, 0);
	}
}
