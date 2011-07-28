package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;

public class SendSimpleProofCommand extends AbstractHandler {

	private static final String PARA_NAME = ZEvesPlugin.PLUGIN_ID + ".proof.simpleCmd.name";
	
	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		String paraValue = event.getParameter(PARA_NAME);
		
		System.out.println("Found para: " + paraValue);
		return null;
	}

}
