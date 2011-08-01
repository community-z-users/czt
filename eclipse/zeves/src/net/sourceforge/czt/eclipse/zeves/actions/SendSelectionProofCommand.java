package net.sourceforge.czt.eclipse.zeves.actions;

import java.io.IOException;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesResultConverter;
import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ProofResultElement;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.handlers.HandlerUtil;


public class SendSelectionProofCommand extends SendProofCommand {

	@Override
	protected String getCommand(ExecutionEvent event, String proofCommand,
			ProofResultElement proofResult) {
		
		ISelection selection = HandlerUtil.getCurrentSelection(event);
		if (selection.isEmpty()) {
			return null;
		}
		
		if (!(selection instanceof ITextSelection)) {
			return null;
		}
		
		ITextSelection textSel = (ITextSelection) selection;
		ZEditor editor = proofResult.getEditor();
		
		String selectedText = textSel.getText();
		SectionManager sectInfo = editor.getParsedData().getSectionManager().clone();
		String sectName = proofResult.getSectionName();
		
		Term selTerm = parseSelection(editor.getSite().getShell(), selectedText, sectInfo, sectName);
		
		if (selTerm == null) {
			return null;
		}
		
		String param = ZEvesResultConverter.printResult(sectInfo, sectName, selTerm,
				editor.getMarkup(), -1);
		
		return String.format(proofCommand, param.trim());
	}
	
	protected Term parseSelection(Shell shell, String selectedText, SectionManager sectInfo,
			String sectName) {
		
		try {
			return ZEvesResultConverter.parseZEvesResult(sectInfo, sectName, selectedText);
		} catch (IOException e) {
			// unexpected exception - log and return
			ZEvesPlugin.getDefault().log(e);
			return null;
		} catch (CommandException e) {
			Throwable cause = e.getCause();
			MessageDialog.openError(shell, "Problems Parsing Selection", cause.getMessage());
			return null;
		}
	}

}
