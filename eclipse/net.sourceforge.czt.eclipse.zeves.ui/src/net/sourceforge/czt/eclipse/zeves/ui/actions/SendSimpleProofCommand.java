package net.sourceforge.czt.eclipse.zeves.ui.actions;

import net.sourceforge.czt.eclipse.zeves.ui.views.ZEditorResults.IProofObject;

import org.eclipse.core.commands.ExecutionEvent;

public class SendSimpleProofCommand extends SendProofCommand {

	@Override
	protected String getCommand(ExecutionEvent event, String proofCommand,
			IProofObject proofResult) {
		return proofCommand;
	}

}
