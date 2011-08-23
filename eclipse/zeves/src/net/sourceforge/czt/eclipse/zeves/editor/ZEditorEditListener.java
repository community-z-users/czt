package net.sourceforge.czt.eclipse.zeves.editor;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.ui.texteditor.ITextEditor;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.actions.SubmitToPointCommand;

public class ZEditorEditListener implements IDocumentListener {

	private final ITextEditor editor;
	
	public ZEditorEditListener(ITextEditor editor) {
		super();
		this.editor = editor;
	}

	@Override
	public void documentChanged(DocumentEvent event) { }
	
	@Override
	public void documentAboutToBeChanged(DocumentEvent event) {
		// undo through to the editing place
		undoThrough(event.getOffset());
	}
	
	private void undoThrough(int editOffset) {
		
		ZEves prover = ZEvesPlugin.getZEves();
		if (!prover.isRunning()) {
			return;
		}
		
        IResource resource = ZEditorUtil.getEditorResource(editor);
        IDocument document = ZEditorUtil.getDocument(editor);
        
        if (resource == null || document == null) {
        	return;
        }
        
        ZEvesFileState fileState = prover.getState(resource, true);
        int submittedOffset = fileState.getLastPositionOffset();
        if (editOffset > submittedOffset) {
        	// editing after last submission - no undo necessary
        	return;
        }
        
        ZEvesAnnotations annotations = new ZEvesAnnotations(editor, resource, document);
        
    	// first delete all the previous markers
		try {
			annotations.deleteMarkers(editOffset);
		} catch (CoreException e) {
			ZEvesPlugin.getDefault().log(e);
		}
		
    	Job job = SubmitToPointCommand.createUndoJob(prover, fileState, editOffset);
    	job.schedule();
	}
	
}
