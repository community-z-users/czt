package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.ProofResultElement;

import org.eclipse.core.commands.ExecutionEvent;

public class SendSimpleProofCommand extends SendProofCommand {

	@Override
	protected String getCommand(ExecutionEvent event, String proofCommand,
			ProofResultElement proofResult) {
		return proofCommand;
	}

}
