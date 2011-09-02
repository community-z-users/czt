package net.sourceforge.czt.eclipse.zeves.core;

import java.util.Map;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.texteditor.ITextEditor;

public class ZEvesUndoCommand implements IZEvesExecCommand {
	
	private final ITextEditor editor;
	private final int offset;
	
	public ZEvesUndoCommand(ITextEditor editor, int offset) {
		this.editor = editor;
		this.offset = offset;
	}
	
	@Override
	public boolean canMerge(IZEvesExecCommand command) {
		if (command instanceof ZEvesUndoCommand) {
			return editor == ((ZEvesUndoCommand) command).editor;
		}
		
		return false;
	}
	
	@Override
	public IZEvesExecCommand merge(IZEvesExecCommand command) {
		if (offset <= ((ZEvesUndoCommand) command).offset) {
			return this;
		} else {
			return command;
		}
	}

	@Override
	public IStatus execute(IProgressMonitor monitor) {
		
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
        
        if (!snapshot.needUndo(filePath, offset)) {
        	// editing after last submission - no undo necessary
        	return Status.OK_STATUS;
        }
		
        ZEvesApi zEvesApi = prover.getApi();
        
		try {
			Map<String, Integer> fileUndoOffsets = 
				snapshot.undoThrough(zEvesApi, filePath, offset);

			ResourceUtil.deleteMarkers(fileUndoOffsets);
			
		} catch (ZEvesException e) {
			return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
		}
		
		return Status.OK_STATUS;
	}
}