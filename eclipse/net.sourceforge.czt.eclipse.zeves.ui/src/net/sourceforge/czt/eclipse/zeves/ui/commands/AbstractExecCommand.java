package net.sourceforge.czt.eclipse.zeves.ui.commands;

import net.sourceforge.czt.eclipse.zeves.core.IZEvesExecCommand;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;

public abstract class AbstractExecCommand implements IZEvesExecCommand {

	@Override
	public boolean canMerge(IZEvesExecCommand command) {
		// by default, merge is not supported
		return false;
	}

	@Override
	public IZEvesExecCommand merge(IZEvesExecCommand command) {
		throw new UnsupportedOperationException();
	}

	@Override
	public IStatus execute(IProgressMonitor monitor) {
		try {
			IStatus result = doExecute(monitor);
			completed(result);
			return result;
		} catch (OperationCanceledException cancelEx) {
			completed(Status.CANCEL_STATUS);
			throw cancelEx;
		}
	}
	
	protected abstract IStatus doExecute(IProgressMonitor monitor);

	protected void completed(IStatus result) {
		// do nothing by default
	}
	
}
