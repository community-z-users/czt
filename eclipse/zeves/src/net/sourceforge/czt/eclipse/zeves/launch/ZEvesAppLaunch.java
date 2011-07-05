package net.sourceforge.czt.eclipse.zeves.launch;

import java.io.IOException;

import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.zeves.ZEvesServer;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;


public class ZEvesAppLaunch extends ZEvesRemoteLaunch {

	public static final String LOCALHOST_ADDRESS = "127.0.0.1";
	
	@Override
	protected String getServerAddress(ILaunchConfiguration configuration) throws CoreException {
		// always locahost for the app
		return LOCALHOST_ADDRESS;
	}

	@Override
	protected void startProver(ILaunchConfiguration configuration, String mode, ILaunch launch,
			IProgressMonitor monitor, ZEves prover, String address, int port) throws CoreException {
		
		if (monitor.isCanceled()) {
			return;
		}
		
		String zEvesExecutable = getVerifyLocation(configuration);

		if (monitor.isCanceled()) {
			return;
		}
		
		monitor.beginTask("Launching " + configuration.getName() + "...", IProgressMonitor.UNKNOWN);

		ZEvesServer server = new ZEvesServer(zEvesExecutable, port);
		try {
			server.start();
		} catch (IOException e) {
			abort("Problems starting Z/Eves application: " + e.getMessage(), e, 0);
			return;
		}
		
		if (monitor.isCanceled()) {
			server.stop();
			return;
		}
		
		boolean started = startProver(prover, address, port, monitor);
		if (!started) {
			server.stop();
			return;
		}
		
		prover.setServer(server);
		
		System.out.println("Done launching");
	}

	private String getVerifyLocation(ILaunchConfiguration configuration) throws CoreException {
		
		String location = getLocationConfig(configuration);
		
		if (location == null || location.isEmpty()) {
			abort("Z/Eves executable is not specified");
		}
		
		// sometimes it is not a file, e.g. "wine zeves.exe"
//		File file = new File(location);
//		if (!file.exists()) {
//			abort("Z/Eves executable does not exist");
//		}
//		
//		// must be a file
//		if (!file.isFile()) {
//			abort("Z/Eves executable location is not a file");
//		}
//		
//		return file;
		return location;
	}
	
	public static String getLocationConfig(ILaunchConfiguration configuration) {
		String location= ""; //$NON-NLS-1$
		try {
			location= configuration.getAttribute(ZEvesLaunchConstants.ATTR_LOCATION, ""); //$NON-NLS-1$
		} catch (CoreException ce) {
			ZEvesPlugin.getDefault().log("Error reading configuration", ce);
		}
		return location;
	}
	
}
