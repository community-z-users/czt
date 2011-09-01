package net.sourceforge.czt.eclipse.zeves.core;

import java.util.Map;

import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesSnapshot.FileSection;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

public class ZEvesUndoSectionCommand implements ZEvesExecCommand {
	
	private final FileSection section;
	
	public ZEvesUndoSectionCommand(FileSection section) {
		this.section = section;
	}
	
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
		if (!prover.isRunning()) {
			return Status.OK_STATUS;
		}

		ZEvesApi zEvesApi = prover.getApi();
        ZEvesSnapshot snapshot = prover.getSnapshot();
        
        boolean success = false;
        try {
			Map<String, Integer> fileUndoOffsets = 
				snapshot.undoThrough(zEvesApi, section);
			
			ResourceUtil.deleteMarkers(fileUndoOffsets);
			success = true;
		} catch (ZEvesException e) {
			return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
		} finally {
			completed(success);
		}
		
		return Status.OK_STATUS;
	}
	
	protected void completed(boolean success) {}
}