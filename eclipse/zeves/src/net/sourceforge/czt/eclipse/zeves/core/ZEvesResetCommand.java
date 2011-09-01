package net.sourceforge.czt.eclipse.zeves.core;

import java.util.Set;

import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

public class ZEvesResetCommand implements ZEvesExecCommand {

	@Override
	public boolean canMerge(ZEvesExecCommand command) {
		return false;
	}

	@Override
	public ZEvesExecCommand merge(ZEvesExecCommand command) {
		throw new UnsupportedOperationException();
	}

	@Override
	public IStatus execute(IProgressMonitor monitor) {
		
		ZEves prover = ZEvesPlugin.getZEves();
		
		// upon reset, reset the API and all the file states
		if (prover.isRunning()) {
			try {
				prover.getApi().reset();
			} catch (ZEvesException e) {
				return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
			}
		}
		
		Set<String> clearedPaths = prover.getSnapshot().clear();

		// also remove all markers
		ResourceUtil.clearMarkers(clearedPaths);
		
		completed();
		
		return Status.OK_STATUS;
	}
	
	protected void completed() {	}
	
}