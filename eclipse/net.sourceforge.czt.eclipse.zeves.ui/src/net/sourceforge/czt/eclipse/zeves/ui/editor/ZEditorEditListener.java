package net.sourceforge.czt.eclipse.zeves.ui.editor;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;

import net.sourceforge.czt.eclipse.ui.document.IResourceDocumentListener;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ZEvesUndoCommand;

/**
 * A document edit listener that undoes Z/EVES Snapshot according to recent
 * document edit. This is necessary, because updates in Z specifications can be
 * changed, and thus things submitted to Z/EVES are no longer valid. The
 * listener keeps the synchronization together with the changes in
 * specification. The Z/EVES snapshot is undone up to the edit in the document.
 * 
 * @author Andrius Velykis
 */
public class ZEditorEditListener implements IResourceDocumentListener {

	@Override
	public boolean isResourceInteresting(IEditorPart editor, IResource resource) {
		// interested in all editors and resources
		// let the undo command resolve what is relevant afterwards
		return editor instanceof ITextEditor;
	}
	
	@Override
	public void documentChanged(IEditorPart editor, IResource resource, DocumentEvent event) { }

	@Override
	public void documentAboutToBeChanged(IEditorPart editor, IResource resource, DocumentEvent event) {
		
		if (!(editor instanceof ITextEditor)) {
			return;
		}
		
		// undo through to the editing place
		undoThrough((ITextEditor) editor, event.getOffset());
	}
	
	private void undoThrough(ITextEditor editor, int editOffset) {
		
		ZEves prover = ZEvesCore.getZEves();
		if (!prover.isRunning()) {
			return;
		}
		
		prover.getExecutor().addCommand(new ZEvesUndoCommand(editor, editOffset));
	}
	
}
