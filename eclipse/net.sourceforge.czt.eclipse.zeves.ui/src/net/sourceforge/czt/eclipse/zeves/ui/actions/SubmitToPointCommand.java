package net.sourceforge.czt.eclipse.zeves.ui.actions;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.util.PlatformUtil;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ZEvesSubmitCommand;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.handlers.HandlerUtil;


public class SubmitToPointCommand extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		IZEditor editor = (IZEditor) HandlerUtil.getActiveEditor(event);
		int caretPosition = ZEditorUtil.getCaretPosition(editor);
		
		submitToOffset(editor, caretPosition);
		return null;
	}

	public static void submitToOffset(final IZEditor editor, final int offset) {
		
		final ZEves prover = ZEvesCore.getZEves();
		if (!prover.isRunning()) {
			MessageDialog.openInformation(editor.getSite().getShell(), "Prover Not Running",
					"The Z/EVES prover is not running.");
			return;
//			throw new ExecutionException("Prover is not running");
		}
		
		prover.getExecutor().addCommand(new ZEvesSubmitCommand(editor, offset) {
			@Override
			protected void completed(IStatus result) {
				// set caret position in display thread
				PlatformUtil.runInUI(new Runnable() {
					@Override
					public void run() {
						ZEditorUtil.setCaretPosition(editor, offset);
						editor.getSite().getPage().activate(editor);
					}
				});
			}
		});
	}
}
