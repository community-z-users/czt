package net.sourceforge.czt.eclipse.zeves.ui.launch;

import java.io.File;
import java.io.IOException;

import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
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
		File workingDir = getVerifyWorkingDir(configuration);

		if (monitor.isCanceled()) {
			return;
		}
		
		monitor.beginTask("Launching " + configuration.getName() + "...", IProgressMonitor.UNKNOWN);

		ZEvesServer server = new ZEvesServer(zEvesExecutable, port, workingDir);
		try {
			server.start();
		} catch (IOException e) {
			abort("Problems starting Z/EVES application: " + e.getMessage(), e, 0);
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
		
		// init launch in the process support
		ZEvesUIPlugin.getZEvesProcessSupport().initLaunch(configuration);
		
		System.out.println("Done launching");
	}

	private String getVerifyLocation(ILaunchConfiguration configuration) throws CoreException {
		
		String location = getLocationConfig(configuration);
		
		if (location == null || location.isEmpty()) {
			abort("Z/EVES executable is not specified");
		}
		
		// sometimes it is not a file, e.g. "wine zeves.exe"
//		File file = new File(location);
//		if (!file.exists()) {
//			abort("Z/EVES executable does not exist");
//		}
//		
//		// must be a file
//		if (!file.isFile()) {
//			abort("Z/EVES executable location is not a file");
//		}
//		
//		return file;
		return location;
	}
	
  private File getVerifyWorkingDir(ILaunchConfiguration configuration) throws CoreException
  {

    String location = getWorkingDirConfig(configuration);

    if (location != null && location.isEmpty()) {
      location = null;
    }

    if (location == null) {
      return null;
    }

    File file = new File(location);
    if (!file.exists()) {
      abort("Z/EVES working directory does not exist");
    }

    // must be a directory
    if (!file.isDirectory()) {
      abort("Z/EVES working directory is not a directory");
    }

    return file;
  }
	
	public static String getLocationConfig(ILaunchConfiguration configuration) {
		String location= ""; //$NON-NLS-1$
		try {
			location= configuration.getAttribute(ZEvesLaunchConstants.ATTR_LOCATION, ""); //$NON-NLS-1$
		} catch (CoreException ce) {
			ZEvesUIPlugin.getDefault().log("Error reading configuration", ce);
		}
		return location;
	}
	
  public static String getWorkingDirConfig(ILaunchConfiguration configuration)
  {
    String location = null; //$NON-NLS-1$
    try {
      location = configuration.getAttribute(ZEvesLaunchConstants.ATTR_WORKING_DIR, (String) null); //$NON-NLS-1$
    }
    catch (CoreException ce) {
      ZEvesUIPlugin.getDefault().log("Error reading configuration", ce);
    }
    return location;
  }
	
}
