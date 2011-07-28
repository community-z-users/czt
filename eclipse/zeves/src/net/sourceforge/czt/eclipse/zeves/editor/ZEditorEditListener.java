package net.sourceforge.czt.eclipse.zeves.editor;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.texteditor.ITextEditor;

import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

public class ZEditorEditListener implements IDocumentListener {

	private final ITextEditor editor;
	
	public ZEditorEditListener(ITextEditor editor) {
		super();
		this.editor = editor;
	}

	@Override
	public void documentChanged(DocumentEvent event) {}
	
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
        ZEvesApi zEvesApi = prover.getApi();
        
    	// first delete all the previous markers
		try {
			annotations.deleteMarkers(editOffset);
		} catch (CoreException e) {
			ZEvesPlugin.getDefault().log(e);
		}
    	
    	// actually undoing - current position has been submitted before
    	Job job = createUndoJob(zEvesApi, fileState, editOffset);
		
		job.setUser(true);
		// TODO set scheduling rule to avoid interference
		job.schedule();
	}
	
	private Job createUndoJob(final ZEvesApi zEvesApi, final ZEvesFileState fileState, 
			final int undoOffset) {
		
		Job job = new Job("Undoing in Z/Eves") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				
				try {
					fileState.undoThrough(zEvesApi, new Position(undoOffset, 0));
				} catch (ZEvesException e) {
					return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
				}
				
				return Status.OK_STATUS;
			}
		};
		return job;
	}
	
}
