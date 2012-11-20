package net.sourceforge.czt.eclipse.zeves.core;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;

public interface IZEvesExecCommand {
	
	public boolean canMerge(IZEvesExecCommand command);
	
	public IZEvesExecCommand merge(IZEvesExecCommand command);
	
	public IStatus execute(IProgressMonitor monitor);
}