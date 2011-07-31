package net.sourceforge.czt.eclipse.zeves.actions;

import java.util.Timer;
import java.util.TimerTask;

import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.editor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesAnnotations;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesExecVisitor;
import net.sourceforge.czt.eclipse.zeves.editor.ZEvesExecVisitor.CancelException;
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
		
		ZEditor editor = (ZEditor) HandlerUtil.getActiveEditor(event);
		int caretPosition = ZEditorUtil.getCaretPosition(editor);
		
		submitToOffset(editor, editor.getParsedData(), caretPosition);
		return null;
	}

	public static void submitToOffset(ZEditor editor, ParsedData parsedData, int offset)
			throws ExecutionException {
		
		ZEves prover = ZEvesPlugin.getZEves();
		if (!prover.isRunning()) {
			throw new ExecutionException("Prover is not running");
		}
		
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

        int dirtyOffset;
        Job job = null;
        if (offset <= submittedOffset) {
        	dirtyOffset = offset;
        	// actually undoing - current position has been submitted before
			// FIXME temporary thing - running it sync for now, make parallel afterwards
        	try {
				fileState.undoThrough(zEvesApi, new Position(offset, 0));
			} catch (ZEvesException e) {
				throw new ExecutionException(e.getMessage(), e);
			}
//        	job = createUndoJob(zEvesApi, fileState, offset);
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
        	
        	job = createSubmitJob(editor, parsedData, annotations, zEvesApi, 
        			fileState, start, offset);
        }
        
		// first delete all the previous markers in the dirty region
		try {
			annotations.deleteMarkers(dirtyOffset);
		} catch (CoreException e) {
			ZEvesPlugin.getDefault().log(e);
		}
		

		
		if (job != null) {
			// now run the exec job
			job.setUser(true);
			job.schedule();
		}
	}

	private static Job createSubmitJob(final ZEditor editor, final ParsedData parsedData,
			final ZEvesAnnotations annotations, final ZEvesApi zEvesApi,
			final ZEvesFileState fileState, final int start, final int end) {
		
		Job job = new Job("Sending to Z/Eves") {
			@Override
			protected IStatus run(final IProgressMonitor monitor) {
				
				Timer cancelMonitor = initCancelMonitor(zEvesApi, monitor);
				
				final ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
						zEvesApi, fileState, 
						annotations, parsedData.getSectionManager(), 
						start, end, monitor);
				
				try {
					zEvesExec.execSpec(parsedData.getSpec());
				} catch (CancelException e) {
					// cancelled
					return Status.CANCEL_STATUS;
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
		return job;
	}
	
//	private static Job createUndoJob(final ZEvesApi zEvesApi, final ZEvesFileState fileState, 
//			final int undoOffset) {
//		
//		Job job = new Job("Undoing in Z/Eves") {
//			@Override
//			protected IStatus run(IProgressMonitor monitor) {
//				
//				try {
//					fileState.undoThrough(zEvesApi, new Position(undoOffset, 0));
//				} catch (ZEvesException e) {
//					return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
//				}
//				
//				return Status.OK_STATUS;
//			}
//		};
//		return job;
//	}
}
