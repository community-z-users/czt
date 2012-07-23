package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.core.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesSubmitNextCommand;

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
		
		final ZEditor editor = (ZEditor) HandlerUtil.getActiveEditor(event);
		
		final ZEves prover = ZEvesPlugin.getZEves();
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
	
	public static void updateCaretOnNext(final ZEditor editor) {
		IResource resource = ZEditorUtil.getEditorResource(editor);
		if (resource == null) {
			return;
		}
		
		String filePath = ResourceUtil.getPath(resource);
		final int lastOffset = ZEvesPlugin.getZEves().getSnapshot().getLastPositionOffset(filePath);
		
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
