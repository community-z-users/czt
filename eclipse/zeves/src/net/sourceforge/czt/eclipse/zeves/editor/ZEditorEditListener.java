package net.sourceforge.czt.eclipse.zeves.editor;

import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.ui.texteditor.ITextEditor;

import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesUndoCommand;

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
		
		prover.getExecutor().addCommand(new ZEvesUndoCommand(editor, editOffset));
	}
	
}
