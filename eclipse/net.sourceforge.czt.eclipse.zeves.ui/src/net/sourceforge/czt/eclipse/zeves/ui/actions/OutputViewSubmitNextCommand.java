package net.sourceforge.czt.eclipse.zeves.ui.actions;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.views.IZInfoObject;
import net.sourceforge.czt.eclipse.zeves.core.ZEves;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesCore;
import net.sourceforge.czt.eclipse.zeves.ui.commands.ZEvesSubmitNextCommand;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEvesOutputView;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IZEditorObject;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.handlers.HandlerUtil;


public class OutputViewSubmitNextCommand extends AbstractHandler {

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
		final int elemEnd = elemPos.getOffset() + elemPos.getLength();
		
		// add a "next" command starting from after the currently selected position
		prover.getExecutor().addCommand(new ZEvesSubmitNextCommand(editor) {
			
			@Override
			protected int getStartOffset(int submittedOffsetInFile) {
				return elemEnd + 1;
			}

			@Override
			protected void completed(IStatus result) {
				EditorSubmitNextCommand.updateCaretOnNext(editor);
			}
		});
		
		return null;
	}
}
