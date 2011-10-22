package net.sourceforge.czt.eclipse.zeves.editor;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.eclipse.CZTPlugin;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;


public class ZEditorEditTracker {

	private static final String ZEDITOR_ID = CZTPlugin.getPluginID() + ".editors.zeditor.ZEditor";
	
	private final Map<ITextEditor, IDocumentListener> editorListeners = 
			new HashMap<ITextEditor, IDocumentListener>();
	
	public void init() {
		Display.getDefault().syncExec(new Runnable() {
			
			@Override
			public void run() {
				PlatformUI.getWorkbench().getActiveWorkbenchWindow().getPartService()
						.addPartListener(partListener);
			}
		});
	}
	
	public void dispose() {
		removePartListener();
		
		for (ITextEditor editor : editorListeners.keySet()) {
			removeListener(editor);
		}
		editorListeners.clear();
	}
	
	private void removePartListener() {
		
		IWorkbench workbench = PlatformUI.getWorkbench();
		if (workbench == null) {
			return;
		}
		
		IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
		if (window == null) {
			return;
		}
		
		window.getPartService().removePartListener(partListener);
	}
	
	private IDocumentListener getListener(ITextEditor editor, boolean create) {
		
		IDocumentListener listener = editorListeners.get(editor);
		if (listener == null && create) {
			listener = new ZEditorEditListener(editor);
			editorListeners.put(editor, listener);
		}
		
		return listener;
	}
	
	private ITextEditor getZEditor(IWorkbenchPartReference ref) {
		if (!ZEDITOR_ID.equals(ref.getId())) {
			return null;
		}
		
		return (ITextEditor) ref.getPart(false);
	}
	
	private void removeListener(ITextEditor editor) {
		IDocumentListener listener = getListener(editor, false);
		if (listener != null) {
			IDocument document = ZEditorUtil.getDocument(editor);
			if (document != null) {
				document.removeDocumentListener(listener);
			}
		}
	}
	
    /*
     * @see IPartListener2
     */
	private IPartListener2 partListener = new IPartListener2() {
		
		public void partVisible(IWorkbenchPartReference ref) {
		}

		public void partHidden(IWorkbenchPartReference ref) {
		}

		public void partInputChanged(IWorkbenchPartReference ref) {
		}

		public void partActivated(IWorkbenchPartReference ref) {
			ITextEditor editor = getZEditor(ref);
			if (editor != null) {
				IDocumentListener listener = getListener(editor, true);
				IDocument document = ZEditorUtil.getDocument(editor);
				document.addDocumentListener(listener);
			}
		}

		public void partBroughtToTop(IWorkbenchPartReference ref) {
		}

		public void partClosed(IWorkbenchPartReference ref) {
			ITextEditor editor = getZEditor(ref);
			if (editor != null) {
				removeListener(editor);
			}
		}

		public void partDeactivated(IWorkbenchPartReference ref) {
		}

		public void partOpened(IWorkbenchPartReference ref) {
		}
	};
	
}
