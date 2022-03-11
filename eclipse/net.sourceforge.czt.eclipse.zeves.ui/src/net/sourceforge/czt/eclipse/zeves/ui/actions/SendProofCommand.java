package net.sourceforge.czt.eclipse.zeves.ui.actions;

import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEvesOutputView;
import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IProofObject;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;
import net.sourceforge.czt.zeves.util.ZEvesString;

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

	private static final String PARAM_CMD_NAME = ZEvesUIPlugin.PLUGIN_ID + ".proof.cmdName";
	
	private static final String DEFAULT_IDENT = "  ";
	
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
		IProofObject proofResult = outputView.getCurrentProof();
		if (proofResult == null) {
			MessageDialog.openError(shell, "Invalid element", "Proof commands must be executed on proof goals.");
			return null;
		}
		
		String proofCommand = getCommand(event, proofCommandName, proofResult);
		if (proofCommand == null) {
			return null;
		}
		
		addSubmitCommand(proofResult, proofCommand);
		
		return null;
	}

	public static void addSubmitCommand(IProofObject proofResult, String proofCommand)
			throws ExecutionException {
		
		// insert the command after the proof result position into the editor
		Position pos = proofResult.getPosition();
		final IZEditor editor = proofResult.getEditor();
		IDocument document = ZEditorUtil.getDocument(editor);
		
		if (pos == null || document == null) {
			// invalid
			return;
		}
		
		String separator = ZEvesString.ZPROOFCOMMANDSEP + "\n";
		String cmdWithSep;
		final int addOffset;
		if (proofResult.getZEvesStepIndex() == ZEvesSnapshot.GOAL_STEP_INDEX) {
			// if the goal (use default indent)
			cmdWithSep = DEFAULT_IDENT + proofCommand + separator;
			addOffset = DEFAULT_IDENT.length() + 1;
		} else {
			
			String indent = getIndent(document, pos);
			cmdWithSep = separator + indent + proofCommand;
			addOffset = separator.length() + indent.length() + 1;
		}
		
		final int posEnd = pos.getOffset() + pos.getLength();
		try {
			document.replace(posEnd, 0, cmdWithSep);
		} catch (BadLocationException e) {
			ZEvesUIPlugin.getDefault().log(e);
		}
		
		// ask the editor to reconcile to avoid waiting for the 
		// delayed reconciler to kick in
		editor.forceReconcile();
		
		SubmitToPointCommand.submitToOffset(editor, posEnd + addOffset);
	}

	private static String getIndent(IDocument document, Position pos) {
		
		String indent = "";
		try {
			int prevLine = document.getLineOfOffset(pos.getOffset());
			int prevLineOffset = document.getLineOffset(prevLine);
			String textToPos = document.get(prevLineOffset, pos.getOffset() - prevLineOffset);
			StringBuilder out = new StringBuilder();
			for (int index = 0; index < textToPos.length(); index++) {
				char c = textToPos.charAt(index);
				if (Character.isWhitespace(c)) {
					// take all whitespace at the start - it will be the indent to repeat
					out.append(c);
				} else {
					break;
				}
			}
			indent = out.toString();
		} catch (BadLocationException e) {
			ZEvesUIPlugin.getDefault().log(e);
		}
		return indent;
	}
	
	protected abstract String getCommand(ExecutionEvent event, String proofCommand,
			IProofObject proofResult);

}
