package net.sourceforge.czt.eclipse.zeves.core;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;

public interface ZEvesExecCommand {
	
	public boolean canMerge(ZEvesExecCommand command);
	
	public ZEvesExecCommand merge(ZEvesExecCommand command);
	
	public IStatus execute(IProgressMonitor monitor);
}