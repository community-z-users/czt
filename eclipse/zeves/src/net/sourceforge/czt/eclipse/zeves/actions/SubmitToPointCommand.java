package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.editor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesAnnotations;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesExecVisitor;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.handlers.HandlerUtil;


public class SubmitToPointCommand extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		ZEves prover = ZEvesPlugin.getZEves();
		if (!prover.isRunning()) {
			throw new ExecutionException("Prover is not running");
		}
		
		ZEditor editor = (ZEditor) HandlerUtil.getActiveEditor(event);
		final ParsedData parsedData = editor.getParsedData();
		
        IResource resource = ZEditorUtil.getEditorResource(editor);
        IDocument document = ZEditorUtil.getDocument(editor);
        
        final ZEvesAnnotations annotations;
        if (resource != null) {
        	annotations = new ZEvesAnnotations(editor, resource, document);
        	
			// first delete all the previous markers
			try {
				annotations.clearMarkers();
			} catch (CoreException e) {
				ZEvesPlugin.getDefault().log(e);
			}
			
        } else {
        	annotations = null;
        }
        
        final ZEvesApi zEvesApi = prover.getApi();
        
        final int start = 0;
        final int caretPosition = ZEditorUtil.getCaretPosition(editor);
        // TODO handle if resource is not available
		final ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
				zEvesApi, prover.getState(resource, true), 
				annotations, start,	caretPosition);
        
		Job job = new Job("Sending to Z/Eves") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				
				try {
					
					zEvesApi.reset();
					zEvesExec.execSpec(parsedData.getSpec());
					
//					zEvesApi.undoBackTo(5);
//					int historyCount = zEvesApi.getHistoryLength();
//					System.out.println("History count: " + zEvesApi.getHistoryLength());
//					System.out.println("Last elem: " + zEvesApi.getHistoryElement(historyCount));
//					System.out.println("InitIsOk proved: " + zEvesApi.getGoalProvedState("InitIsOK"));
					
				} catch (ZEvesException e) {
					return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
				} finally {
					zEvesExec.finish();
				}
				
				return Status.OK_STATUS;
			}
		};
		
		job.setUser(true);
		job.schedule();
		
		return null;
	}
}
