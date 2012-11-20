package net.sourceforge.czt.eclipse.zeves.ui.launch;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.zeves.ZEvesServer;
import net.sourceforge.czt.zeves.ZEvesServerEvent;
import net.sourceforge.czt.zeves.ZEvesServerListener;

public class ZEvesProcessSupport {

	private ILaunchConfiguration launchConfig;
	private ZEvesServer lastServer;
	
	private final ZEvesServerListener serverListener = new ZEvesServerListener() {
		
		@Override
		public void serverStopped(ZEvesServerEvent event) {
			if (!event.isUser()) {
				// server died - notify the user
				notifyServerDied();
			}
		}

		@Override
		public void serverStarted(ZEvesServerEvent event) {}
	};
	
	public void initLaunch(ILaunchConfiguration launchConfig) {
		this.launchConfig = launchConfig;
		
		ZEves prover = ZEvesCore.getZEves();
		
		if (lastServer != null) {
			lastServer.removeServerListener(serverListener);
		}
		
		lastServer = prover.getServer();
		if (lastServer != null) {
			lastServer.addServerListener(serverListener);
		}
	}
	
	public void restart() {
		
		stop();
		
		if (launchConfig != null) {
			PlatformUtil.runInUI(new Runnable() {
				@Override
				public void run() {
					DebugUITools.launch(launchConfig, ILaunchManager.RUN_MODE);
				}
			});
		}
	}
	
	public void stop() {
		ZEves prover = ZEvesCore.getZEves();
		prover.stop();
	}
	
	public void dispose() {
		if (lastServer != null) {
			lastServer.removeServerListener(serverListener);
		}
	}
	
	private void notifyServerDied() {
		PlatformUtil.runInUI(new Runnable() {
			@Override
			public void run() {
				
				MessageDialog dialog = new MessageDialog(getShell(), "Z/EVES Prover Terminated", null, 
						"The Z/EVES prover process has been terminated. Do you want to restart the prover?",
						MessageDialog.ERROR, new String[] {"Restart Prover", "Terminate Prover"}, 0) {
					
					@Override
					public int open() {
						setShellStyle(getShellStyle() | SWT.SHEET);
						return super.open();
					}
				};
				
				if (dialog.open() == 0) {
					restart();
				} else {
					stop();
				}
			}
		});
	}
	
	private Shell getShell() {
		IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		if (window != null) {
			return window.getShell();
		}
		
		return null;
	}
	
}
