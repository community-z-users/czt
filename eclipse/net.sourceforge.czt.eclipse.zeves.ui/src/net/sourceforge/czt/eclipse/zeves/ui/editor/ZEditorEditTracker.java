package net.sourceforge.czt.eclipse.zeves.ui.editor;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.document.IResourceDocumentListener;

/**
 * A document edit tracker that uses {@link ZEditorEditListener} to track
 * changes in open editors. The current implementation reuses
 * DocumentEditTracker in {@link CztUIPlugin}.
 * 
 * @author Andrius Velykis
 */
public class ZEditorEditTracker {

	private final IResourceDocumentListener editListener = new ZEditorEditListener();
	
	public void init() {
		CztUIPlugin.getEditTracker().addEditListener(editListener);
	}
	
	public void dispose() {
		CztUIPlugin.getEditTracker().removeEditListener(editListener);
	}
	
}
