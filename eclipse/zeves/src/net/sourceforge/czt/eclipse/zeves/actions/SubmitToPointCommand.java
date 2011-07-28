package net.sourceforge.czt.eclipse.zeves.actions;

import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
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
import org.eclipse.jface.text.Position;
import org.eclipse.ui.handlers.HandlerUtil;


public class SubmitToPointCommand extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		ZEves prover = ZEvesPlugin.getZEves();
		if (!prover.isRunning()) {
			throw new ExecutionException("Prover is not running");
		}
		
		ZEditor editor = (ZEditor) HandlerUtil.getActiveEditor(event);
		ParsedData parsedData = editor.getParsedData();
		
        IResource resource = ZEditorUtil.getEditorResource(editor);
        IDocument document = ZEditorUtil.getDocument(editor);
        
        ZEvesAnnotations annotations = null;
        if (resource != null) {
        	annotations = new ZEvesAnnotations(editor, resource, document);
        }
        
        ZEvesApi zEvesApi = prover.getApi();
        // TODO handle if resource is not available
        ZEvesFileState fileState = prover.getState(resource, true);
        int submittedOffset = fileState.getLastPositionOffset();
        
        int caretPosition = ZEditorUtil.getCaretPosition(editor);

        int dirtyOffset;
        Job job;
        if (caretPosition <= submittedOffset) {
        	dirtyOffset = caretPosition;
        	// actually undoing - current position has been submitted before
        	job = createUndoJob(zEvesApi, fileState, caretPosition);
        } else {
        	
        	int start;
        	if (submittedOffset < 0) {
        		// nothing submitted - go from start
        		start = 0;
        	} else {
        		// start from the next symbol
        		start = submittedOffset + 1;
        	}
        	
        	dirtyOffset = start;
        	
        	job = createSubmitJob(parsedData, annotations, zEvesApi, 
        			fileState, start, caretPosition);
        }
        
		// first delete all the previous markers in the dirty region
		try {
			annotations.deleteMarkers(dirtyOffset);
		} catch (CoreException e) {
			ZEvesPlugin.getDefault().log(e);
		}
		
		// now run the exec job
		job.setUser(true);
		job.schedule();
		
		return null;
	}

	private Job createSubmitJob(final ParsedData parsedData, ZEvesAnnotations annotations,
			final ZEvesApi zEvesApi, final ZEvesFileState fileState, int start,
			int end) {
		
		final ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
				zEvesApi, fileState, 
				annotations, parsedData.getSectionManager(), 
				start, end);
        
		Job job = new Job("Sending to Z/Eves") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				
				try {
					zEvesExec.execSpec(parsedData.getSpec());
					
//				} catch (ZEvesException e) {
//					return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
				} finally {
					zEvesExec.finish();
				}
				
				return Status.OK_STATUS;
			}
		};
		return job;
	}
	
	private Job createUndoJob(final ZEvesApi zEvesApi, final ZEvesFileState fileState, 
			final int undoOffset) {
		
		Job job = new Job("Undoing in Z/Eves") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				
				try {
					fileState.undoThrough(zEvesApi, new Position(undoOffset, 0));
				} catch (ZEvesException e) {
					return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
				}
				
				return Status.OK_STATUS;
			}
		};
		return job;
	}
}
