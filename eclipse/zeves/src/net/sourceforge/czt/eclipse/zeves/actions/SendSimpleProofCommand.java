package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.zeves.views.ZEditorResults.IProofObject;

import org.eclipse.core.commands.ExecutionEvent;

public class SendSimpleProofCommand extends SendProofCommand {

	@Override
	protected String getCommand(ExecutionEvent event, String proofCommand,
			IProofObject proofResult) {
		return proofCommand;
	}

}
