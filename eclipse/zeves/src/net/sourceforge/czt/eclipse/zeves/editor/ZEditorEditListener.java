package net.sourceforge.czt.eclipse.zeves.editor;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.ui.texteditor.ITextEditor;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.ZEvesSnapshot;
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
        
        ZEvesSnapshot snapshot = prover.getSnapshot();
        String filePath = ResourceUtil.getPath(resource);
        
        if (!snapshot.needUndo(filePath, editOffset)) {
        	// editing after last submission - no undo necessary
        	return;
        }
        
    	Job job = SubmitToPointCommand.createUndoJob(prover, filePath, editOffset);
    	job.schedule();
	}
	
}
