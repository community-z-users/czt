package net.sourceforge.czt.eclipse.zeves.core;

import java.util.Map;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;

public class ZEvesBackCommand extends AbstractExecCommand {
	
	private final ZEditor editor;
	
	public ZEvesBackCommand(ZEditor editor) {
		this.editor = editor;
	}

	@Override
	public IStatus doExecute(IProgressMonitor monitor) {
		
		ZEves prover = ZEvesPlugin.getZEves();
		if (!prover.isRunning()) {
			return Status.OK_STATUS;
		}

        IResource resource = ZEditorUtil.getEditorResource(editor);
        IDocument document = ZEditorUtil.getDocument(editor);
        
        if (resource == null || document == null) {
        	return Status.OK_STATUS;
        }
        
        ZEvesSnapshot snapshot = prover.getSnapshot();
        String filePath = ResourceUtil.getPath(resource);
        
        int lastOffset = snapshot.getLastPositionOffset(filePath);
        if (lastOffset < 0) {
        	// nothing submitted in this editor - cannot go back
        	// TODO undo in other editors?
        	return Status.OK_STATUS;
        }
        
        ZEvesApi zEvesApi = prover.getApi();
        
        // undo through the last offset - this will undo the last result
		try {
			Map<String, Integer> fileUndoOffsets = 
				snapshot.undoThrough(zEvesApi, filePath, lastOffset);

			ResourceUtil.deleteMarkers(fileUndoOffsets);
			
		} catch (ZEvesException e) {
			return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
		}
        
		return Status.OK_STATUS;
	}
	
}