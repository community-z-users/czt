package net.sourceforge.czt.eclipse.zeves.ui.core;

import java.math.BigInteger;
import java.util.Map;
import java.util.Timer;
import java.util.TimerTask;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.ui.compile.IZCompileData;
import net.sourceforge.czt.eclipse.ui.document.IPositionProvider;
import net.sourceforge.czt.eclipse.ui.document.TermPositionProvider;
import net.sourceforge.czt.eclipse.ui.editors.IZEditor;
import net.sourceforge.czt.eclipse.ui.editors.zeditor.ZEditorUtil;
import net.sourceforge.czt.eclipse.ui.editors.zeditor.ZEditorUtil.ReconcileRunnable;
import net.sourceforge.czt.eclipse.zeves.ui.ZEvesUIPlugin;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.IDocument;

public abstract class AbstractSubmitCommand extends AbstractExecCommand {
	
	private final IZEditor editor;
	private final BigInteger documentVersion;
	
	private final Object waitObj = new Object();
	private IZCompileData parsedData = null;
	private boolean reconciled = false;
	
	public AbstractSubmitCommand(IZEditor editor) {
		this.editor = editor;
		this.documentVersion = editor.getDocumentVersion();
	}
	
	@Override
	public IStatus doExecute(IProgressMonitor monitor) {
		
		ZEves prover = ZEvesUIPlugin.getZEves();
		if (!prover.isRunning()) {
			return ZEvesUIPlugin.newErrorStatus("Z/EVES prover is not running.", null);
		}
		
		final ZEvesApi zEvesApi = prover.getApi();
		
		IResource resource = ZEditorUtil.getEditorResource(editor);
		IDocument document = ZEditorUtil.getDocument(editor);
        
        // TODO handle if resource is not available
        String filePath = ResourceUtil.getPath(resource);
		
        ZEvesSnapshot snapshot = ZEvesUIPlugin.getZEves().getSnapshot();
        int submittedOffsetInFile = snapshot.getLastPositionOffset(filePath);
        
        int start = getStartOffset(submittedOffsetInFile);
        if (start - submittedOffsetInFile > 1) {
        	// a gap between last submit and new start - make lastSubmit + 1 the start
        	start = submittedOffsetInFile + 1;
        }
        
        int end = getEndOffset(document);
        
        if (start < 0) {
        	// adjust to start of the document
        	start = 0;
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
				return ZEvesUIPlugin.newErrorStatus(e.getMessage(), e);
			}
		}
		
		if (end <= submittedOffsetInFile) {
			// undo only
			return Status.OK_STATUS;
		}
		
		if (monitor.isCanceled()) {
    		return Status.CANCEL_STATUS;
    	}
		
		/*
		 * ask the editor to reconcile - this is done for several reasons.
		 * First, updates could have been done right before the submit and we
		 * require an up-to-date AST to perform the submit. Forcing reconcile
		 * allows us to avoid waiting for the delayed reconciler to kick in.
		 * 
		 * Secondly, the option to reconcile on parse ("parse automatically")
		 * may have been switched off for the Z Editor. For this reason, we
		 * need to force reconcile manually to get an AST altogether.
		 */
		editor.forceReconcile();
		
		// wait until reconcile completes
    	ZEditorUtil.runOnReconcile(editor, documentVersion, new ReconcileRunnable() {
			@Override
			protected void run(IZCompileData parsedData) {
				synchronized(waitObj) {
					
					AbstractSubmitCommand.this.parsedData = parsedData;
					AbstractSubmitCommand.this.reconciled = true;
					
					waitObj.notify();
				}
			}
		});

    	synchronized (waitObj) {
    		while (!reconciled) {
        		try {
					waitObj.wait();
				} catch (InterruptedException e) {}
        	}
		}
    	
    	if (monitor.isCanceled()) {
    		return Status.CANCEL_STATUS;
    	}
		
		Timer cancelMonitor = initCancelMonitor(zEvesApi, monitor);
		
		IPositionProvider<Term> posProvider = new TermPositionProvider(document);
		ZEvesMarkers markers = resource != null ? new ZEvesMarkers(resource, document) : null;
		
		SectionManager sectInfo = parsedData.getSectionManager();
		Spec specification = parsedData.getSpec();
		
		// wrap into try-finally, because OperationCanceledExpression
		// may be thrown from inside
		try {
			
			return submitSpec(monitor, zEvesApi, filePath, snapshot, start, end, 
					posProvider, markers, document, sectInfo, specification);
			
		} finally {
			cancelMonitor.cancel();
		}
	}
	
	protected abstract int getStartOffset(int submittedOffsetInFile);
	
	protected abstract int getEndOffset(IDocument document);
	
	protected abstract IStatus submitSpec(IProgressMonitor monitor, ZEvesApi zEvesApi,
			String filePath, ZEvesSnapshot snapshot, int start, int end,
			IPositionProvider<Term> posProvider, ZEvesMarkers markers, IDocument document,
			SectionManager sectInfo, Spec specification);

	private Timer initCancelMonitor(final ZEvesApi zEvesApi, final IProgressMonitor monitor) {
		
		// if user cancels the task, check that in a separate thread,
		// because the main thread may be blocked by Z/EVES comms. Then
		// send abort to abort long-running Z/EVES task probably.
		final Timer timer = new Timer(true);
		TimerTask cancelMonitor = new TimerTask() {
			
			@Override
			public void run() {
				if (monitor.isCanceled()) {
					// send abort
					// Z/EVES abort crashes the prover if executed on proof tasks at the moment
					// TODO investigate and reinstate Z/EVES abort
//					zEvesApi.sendAbort();
					timer.cancel();
				}
			}
		};
		// check for cancelation every 0.5 sec 
		int period = 500;
		timer.schedule(cancelMonitor, period, period);
		
		return timer;
	}
}