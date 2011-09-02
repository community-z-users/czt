package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.views.IZInfoObject;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.views.ZEvesOutputView;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ZEvesProofObject;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;


public abstract class SendProofCommand extends AbstractHandler {

	private static final String PARAM_CMD_NAME = ZEvesPlugin.PLUGIN_ID + ".proof.cmdName";
	
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		String proofCommandName = event.getParameter(PARAM_CMD_NAME);
		
		IWorkbenchPart part = HandlerUtil.getActivePart(event);
		if (!(part instanceof ZEvesOutputView)) {
			System.out.println("Not output view");
			return null;
		}
		
		Shell shell = HandlerUtil.getActiveShell(event);
		
		ZEvesOutputView outputView = (ZEvesOutputView) part;
		IZInfoObject currentInput = outputView.getCurrentInput();
		if (!(currentInput instanceof ZEvesProofObject)) {
			MessageDialog.openError(shell, "Invalid element", "Proof commands must be executed on proof goals.");
			return null;
		}
		
		ZEvesProofObject proofResult = (ZEvesProofObject) currentInput;
		
		String proofCommand = getCommand(event, proofCommandName, proofResult);
		if (proofCommand == null) {
			return null;
		}
		
		addSubmitCommand(proofResult, proofCommand);
		
		return null;
	}

	public static void addSubmitCommand(ZEvesProofObject proofResult, String proofCommand)
			throws ExecutionException {
		
		// insert the command after the proof result position into the editor
		Position pos = proofResult.getPosition();
		final ZEditor editor = proofResult.getEditor();
		IDocument document = ZEditorUtil.getDocument(editor);
		
		if (pos == null || document == null) {
			// invalid
			return;
		}
		
		// TODO reference proof separator somewhere?
		String separator = ";\n";
		String cmdWithSep;
		final int addOffset;
		if (proofResult.isGoal()) {
			cmdWithSep = proofCommand + separator;
			addOffset = 1;
		} else {
			cmdWithSep = separator + proofCommand;
			addOffset = separator.length() + 1;
		}
		
		final int posEnd = pos.getOffset() + pos.getLength();
		try {
			document.replace(posEnd, 0, cmdWithSep);
		} catch (BadLocationException e) {
			ZEvesPlugin.getDefault().log(e);
		}
		
		// ask the editor to reconcile to avoid waiting for the 
		// delayed reconciler to kick in
		editor.forceReconcile();
		
		SubmitToPointCommand.submitToOffset(editor, posEnd + addOffset);
	}
	
	protected abstract String getCommand(ExecutionEvent event, String proofCommand,
			ZEvesProofObject proofResult);

}
