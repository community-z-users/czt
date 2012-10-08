package net.sourceforge.czt.eclipse.zeves.ui.editor;

import net.sourceforge.czt.eclipse.ui.CZTPlugin;
import net.sourceforge.czt.eclipse.ui.editors.zeditor.IResourceDocumentListener;

/**
 * A document edit tracker that uses {@link ZEditorEditListener} to track
 * changes in open editors. The current implementation reuses
 * DocumentEditTracker in {@link CZTPlugin}.
 * 
 * @author Andrius Velykis
 */
public class ZEditorEditTracker {

	private final IResourceDocumentListener editListener = new ZEditorEditListener();
	
	public void init() {
		CZTPlugin.getEditTracker().addEditListener(editListener);
	}
	
	public void dispose() {
		CZTPlugin.getEditTracker().removeEditListener(editListener);
	}
	
}
