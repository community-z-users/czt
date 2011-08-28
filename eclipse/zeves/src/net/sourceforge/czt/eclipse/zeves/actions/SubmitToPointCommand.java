package net.sourceforge.czt.eclipse.zeves.actions;

import java.util.Timer;
import java.util.TimerTask;

import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
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
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.handlers.HandlerUtil;


public class SubmitToPointCommand extends AbstractHandler {

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {
		
		ZEditor editor = (ZEditor) HandlerUtil.getActiveEditor(event);
		int caretPosition = ZEditorUtil.getCaretPosition(editor);
		
		submitToOffset(editor, caretPosition);
		return null;
	}

	public static void submitToOffset(ZEditor editor, int offset) {
		
		ZEves prover = ZEvesPlugin.getZEves();
		if (!prover.isRunning()) {
			MessageDialog.openInformation(editor.getSite().getShell(), "Prover Not Running",
					"The Z/Eves prover is not running.");
			return;
//			throw new ExecutionException("Prover is not running");
		}
		
		ParsedData parsedData = editor.getParsedData();
		
        IResource resource = ZEditorUtil.getEditorResource(editor);
        IDocument document = ZEditorUtil.getDocument(editor);
        
        ZEvesAnnotations annotations = null;
        if (resource != null) {
        	annotations = new ZEvesAnnotations(resource, document);
        }
        
        // TODO handle if resource is not available
        ZEvesFileState fileState = prover.getState(resource, true);
        int submittedOffset = fileState.getLastPositionOffset();

        int dirtyOffset;
        Job job;
        if (offset <= submittedOffset) {
        	dirtyOffset = offset;
        	// actually undoing - current position has been submitted before
        	job = createUndoJob(prover, fileState, offset);
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
        	
        	job = createSubmitJob(editor, parsedData, annotations, prover, 
        			fileState, start, offset);
        }
        
		// first delete all the previous markers in the dirty region
		try {
			annotations.deleteMarkers(dirtyOffset);
		} catch (CoreException e) {
			ZEvesPlugin.getDefault().log(e);
		}
		

		job.schedule();
	}

	private static Job createSubmitJob(final ZEditor editor, final ParsedData parsedData,
			final ZEvesAnnotations annotations, 
			ZEves prover, final ZEvesFileState fileState, final int start, final int end) {
		
		final ZEvesApi zEvesApi = prover.getApi();
		
		Job job = new Job("Sending to Z/Eves") {
			@Override
			protected IStatus run(final IProgressMonitor monitor) {
				
				Timer cancelMonitor = initCancelMonitor(zEvesApi, monitor);
				
				final ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
						zEvesApi, fileState, 
						annotations, parsedData, 
						start, end, monitor);

				// wrap into try-finally, because OperationCanceledExpression
				// may be thrown from inside
				try {
					zEvesExec.execSpec(parsedData.getSpec());
				} finally {
					cancelMonitor.cancel();
					zEvesExec.finish();
				}

				// set caret position in display thread
				editor.getSite().getShell().getDisplay().asyncExec(new Runnable() {
					@Override
					public void run() {
						ZEditorUtil.setCaretPosition(editor, end);
						editor.getSite().getPage().activate(editor);
					}
				});
				
				return Status.OK_STATUS;
			}

			private Timer initCancelMonitor(final ZEvesApi zEvesApi, final IProgressMonitor monitor) {
				
				// if user cancels the task, check that in a separate thread,
				// because the main thread may be blocked by Z/Eves comms. Then
				// send abort to abort long-running Z/Eves task probably.
				final Timer timer = new Timer(true);
				TimerTask cancelMonitor = new TimerTask() {
					
					@Override
					public void run() {
						if (monitor.isCanceled()) {
							// send abort
							zEvesApi.sendAbort();
							timer.cancel();
						}
					}
				};
				// check for cancelation every 0.5 sec 
				int period = 500;
				timer.schedule(cancelMonitor, period, period);
				
				return timer;
			}
		};
		
		job.setRule(prover);
		return job;
	}
	
	public static Job createUndoJob(ZEves prover, final ZEvesFileState fileState, final int undoOffset) {
		
		final ZEvesApi zEvesApi = prover.getApi();
		
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
		job.setRule(prover);
		return job;
	}
}
