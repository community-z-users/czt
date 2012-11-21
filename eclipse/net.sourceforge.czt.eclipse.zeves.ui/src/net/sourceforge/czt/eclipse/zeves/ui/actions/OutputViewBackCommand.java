package net.sourceforge.czt.eclipse.zeves.ui.actions;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.views.IZInfoObject;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ZEvesUndoCommand;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEvesOutputView;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IZEditorObject;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.handlers.HandlerUtil;


public class OutputViewBackCommand extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		final ZEvesOutputView outputView = (ZEvesOutputView) HandlerUtil.getActivePart(event);
		
		IZInfoObject currentInput = outputView.getCurrentInput();
		if (!(currentInput instanceof IZEditorObject)) {
			// unknown input - ignore
			return null;
		}

		IZEditorObject editorElement = (IZEditorObject) currentInput;
		
		ZEves prover = ZEvesCore.getZEves();
		if (!prover.isRunning()) {
			MessageDialog.openInformation(outputView.getSite().getShell(), "Prover Not Running",
					"The Z/EVES prover is not running.");
			return null;
		}
		
		final IZEditor editor = editorElement.getEditor();
		Position elemPos = editorElement.getPosition();
		int elemEnd = elemPos.getOffset() + elemPos.getLength();
		
		// undo through to the end of the element - it will undo the element itself
		prover.getExecutor().addCommand(new ZEvesUndoCommand(editor, elemEnd) {
			@Override
			protected void completed(IStatus result) {
				EditorBackCommand.updateCaretOnBack(editor);
			}
		});
		
		return null;
	}
}
