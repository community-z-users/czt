package net.sourceforge.czt.eclipse.zeves.actions;

import java.util.Map;
import java.util.Timer;
import java.util.TimerTask;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.parser.IPositionProvider;
import net.sourceforge.czt.eclipse.editors.parser.ParsedData;
import net.sourceforge.czt.eclipse.editors.parser.TermPositionProvider;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditor;
import net.sourceforge.czt.eclipse.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.zeves.ResourceUtil;
import net.sourceforge.czt.eclipse.zeves.ZEves;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.ZEvesSnapshot;
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
        
        ZEvesSnapshot snapshot = prover.getSnapshot();
        // TODO handle if resource is not available
        String filePath = ResourceUtil.getPath(resource);
        
        int submittedOffsetInFile = snapshot.getLastPositionOffset(filePath);

        Job job;
        if (offset <= submittedOffsetInFile) {
        	// actually undoing - current position has been submitted before
        	job = createUndoJob(prover, filePath, offset);
        } else {
        	
        	int start;
        	if (submittedOffsetInFile < 0) {
        		// nothing submitted - go from start
        		start = 0;
        	} else {
        		// start from the next symbol
        		start = submittedOffsetInFile + 1;
        	}
        	
        	job = createSubmitJob(editor, parsedData, annotations, prover, 
        			filePath, start, offset);
        }

		job.schedule();
	}

	private static Job createSubmitJob(final ZEditor editor, final ParsedData parsedData,
			final ZEvesAnnotations annotations, 
			ZEves prover, final String filePath, final int start, final int end) {
		
		final ZEvesApi zEvesApi = prover.getApi();
		final ZEvesSnapshot snapshot = prover.getSnapshot();
		final IPositionProvider<Term> posProvider = new TermPositionProvider(ZEditorUtil.getDocument(editor));
		
		Job job = new Job("Sending to Z/Eves") {
			@Override
			protected IStatus run(final IProgressMonitor monitor) {
				
				// first delete all the previous markers in the dirty region
	    		try {
	    			annotations.deleteMarkers(start);
	    		} catch (CoreException e) {
	    			ZEvesPlugin.getDefault().log(e);
	    		}
				
	    		// submitting in a file, which is not the last in the snapshot
	    		// e.g. submit one file partially, then submit another
				if (snapshot.needUndo(filePath, start)) {
					// need to undo until the start, and then submit again
					try {
						
						Map<String, Integer> fileUndoOffsets = 
							snapshot.undoThrough(zEvesApi, filePath, start);
						
						ResourceUtil.deleteMarkers(fileUndoOffsets);
						
					} catch (ZEvesException e) {
						return ZEvesPlugin.newErrorStatus(e.getMessage(), e);
					}
				}
				
				Timer cancelMonitor = initCancelMonitor(zEvesApi, monitor);
				
				final ZEvesExecVisitor zEvesExec = new ZEvesExecVisitor(
						zEvesApi, snapshot, annotations, 
						filePath, posProvider, parsedData.getSectionManager(), 
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
	
	public static Job createUndoJob(final ZEves prover, final String filePath, final int undoOffset) {
		
		final ZEvesApi zEvesApi = prover.getApi();
		final ZEvesSnapshot snapshot = prover.getSnapshot();
		
		Job job = new Job("Undoing in Z/Eves") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				
				try {
					Map<String, Integer> fileUndoOffsets = 
						snapshot.undoThrough(zEvesApi, filePath, undoOffset);

					// and just to make sure, delete markers in the current file from the offset
					Integer currentUndoOffset = fileUndoOffsets.get(filePath);
					if (currentUndoOffset == null || currentUndoOffset > undoOffset) {
						fileUndoOffsets.put(filePath, undoOffset);
					}
					
					ResourceUtil.deleteMarkers(fileUndoOffsets);
					
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
