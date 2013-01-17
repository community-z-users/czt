package net.sourceforge.czt.eclipse.zeves.ui.commands;

import java.util.Map;

import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.texteditor.ITextEditor;


public abstract class AbstractUndoCommand extends AbstractExecCommand {
	
	private final ITextEditor editor;
	
	public AbstractUndoCommand(ITextEditor editor) {
		this.editor = editor;
	}
	
	@Override
	public IStatus doExecute(IProgressMonitor monitor) {
		
		ZEves prover = ZEvesCore.getZEves();
		if (!prover.isRunning()) {
			return Status.OK_STATUS;
		}
		
        IResource resource = ZEditorUtil.getEditorResource(editor);
        IDocument document = ZEditorUtil.getDocument(editor);
        
        if (resource == null || document == null) {
        	return Status.OK_STATUS;
        }
        
        ZEvesSnapshot snapshot = ZEvesCore.getSnapshot();
        String filePath = ResourceUtil.getPath(resource);
        
        int offset = getUndoOffset(filePath);
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
			return ZEvesUIPlugin.newErrorStatus(e.getMessage(), e);
		}
		
		return Status.OK_STATUS;
	}
	
	protected ITextEditor getEditor() {
		return editor;
	}
	
	protected abstract int getUndoOffset(String filePath);
	
}