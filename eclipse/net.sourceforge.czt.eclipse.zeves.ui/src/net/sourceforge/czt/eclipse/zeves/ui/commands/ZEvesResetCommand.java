package net.sourceforge.czt.eclipse.zeves.ui.commands;

import java.util.Set;

import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

public class ZEvesResetCommand extends AbstractExecCommand {

	@Override
	public IStatus doExecute(IProgressMonitor monitor) {
		
		ZEves prover = ZEvesCore.getZEves();
		
		// upon reset, reset the API and all the file states
		if (prover.isRunning()) {
			try {
				prover.getApi().reset();
			} catch (ZEvesException e) {
				return ZEvesUIPlugin.newErrorStatus(e.getMessage(), e);
			}
		}
		
		Set<String> clearedPaths = ZEvesCore.getSnapshot().clear();

		// also remove all markers
		ResourceUtil.clearMarkers(clearedPaths);
		
		return Status.OK_STATUS;
	}
	
}