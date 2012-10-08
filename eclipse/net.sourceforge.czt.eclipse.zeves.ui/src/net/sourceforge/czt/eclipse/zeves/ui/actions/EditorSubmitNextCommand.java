package net.sourceforge.czt.eclipse.zeves.ui.actions;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.core.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.ui.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.ui.core.ZEvesSubmitNextCommand;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.handlers.HandlerUtil;


public class EditorSubmitNextCommand extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		final IZEditor editor = (IZEditor) HandlerUtil.getActiveEditor(event);
		
		final ZEves prover = ZEvesUIPlugin.getZEves();
		if (!prover.isRunning()) {
			MessageDialog.openInformation(editor.getSite().getShell(), "Prover Not Running",
					"The Z/EVES prover is not running.");
			return null;
		}
		
		prover.getExecutor().addCommand(new ZEvesSubmitNextCommand(editor) {
			@Override
			protected void completed(IStatus result) {
				updateCaretOnNext(editor);
			}
		});
		
		return null;
	}
	
	public static void updateCaretOnNext(final IZEditor editor) {
		IResource resource = ZEditorUtil.getEditorResource(editor);
		if (resource == null) {
			return;
		}
		
		String filePath = ResourceUtil.getPath(resource);
		final int lastOffset = ZEvesUIPlugin.getZEves().getSnapshot().getLastPositionOffset(filePath);
		
		// set caret position in display thread
		PlatformUtil.runInUI(new Runnable() {
			@Override
			public void run() {
				ZEditorUtil.setCaretPosition(editor, lastOffset);
				editor.getSite().getPage().activate(editor);
			}
		});
	}
}
