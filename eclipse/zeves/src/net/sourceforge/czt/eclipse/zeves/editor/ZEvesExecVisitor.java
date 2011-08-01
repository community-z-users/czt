package net.sourceforge.czt.eclipse.zeves.editor;

import java.io.IOException;
import java.text.MessageFormat;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;

import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.ZSECTION_BEGIN_PATTERN;
import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.ZSECTION_END_PATTERN;
import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.getParents;

/**
 * Special visitor class to translate top-level Z terms. 
 * Each element in the returned list must be transmitted to the Z/Eves
 * server separately, in the given order.
 */
public class ZEvesExecVisitor extends ZEvesPosVisitor {
	
	private final CZT2ZEvesPrinter zEvesXmlPrinter = new CZT2ZEvesPrinter(null);
	
	private final ZEvesApi api;
	private final ZEvesFileState state;
	private final ZEvesAnnotations annotations;
	private final SectionManager sectInfo;
	private Annotation unprocessedAnn;
	
	private final IProgressMonitor progressMonitor;
	
	private static final long FLUSH_INTERVAL = 500;
	private long lastFlush = 0;
	
	public ZEvesExecVisitor(ZEvesApi api, ZEvesFileState state, ZEvesAnnotations annotations,
			SectionManager sectInfo, int startOffset, int endOffset,
			IProgressMonitor progressMonitor) {
    	
		super(startOffset, endOffset);
		this.api = api;
		this.state = state;
		this.annotations = annotations;
		this.sectInfo = sectInfo;
		
		if (progressMonitor == null) {
			progressMonitor = new NullProgressMonitor();
		}
		
		this.progressMonitor = progressMonitor;
	}

    @Override
	protected void visitZSectHead(ZSect term, Position position) {
    	
    	Annotation unfinishedAnn = markUnfinished(position);
		
		try {
    		String sectionBeginXml = MessageFormat.format(ZSECTION_BEGIN_PATTERN, term.getName(), getParents(term.getParent()));
    		api.send(sectionBeginXml);
    		checkCancelled();
    	} catch (ZEvesException e) {
    		// do not return - just handle and continue into paragraphs
    		handleZEvesException(position, e);
    	} finally {
    		markFinished(unfinishedAnn);
    	}
		
	}

	@Override
	protected void visitZSectEnd(ZSect term, Position position) {
		
		Annotation unfinishedAnn = markUnfinished(position);
		
		try {
    		api.send(ZSECTION_END_PATTERN);
    		checkCancelled();
    	} catch (ZEvesException e) {
    		handleZEvesException(position, e);
    	} finally {
    		markFinished(unfinishedAnn);
    	}
	}

    @Override
	protected void visitPara(Para term, Position pos) {
    	// mark unfinished
    	Annotation unfinishedAnn = markUnfinished(pos);
    	
    	try {
    	
	    	String commandXml = term.accept(zEvesXmlPrinter);
	
	    	try {
				ZEvesOutput output = api.send(commandXml);
				handleResult(pos, output);
				checkCancelled();
			} catch (ZEvesException e) {
				state.addPara(pos, -1, term, e.getMessage(), false);
				handleZEvesException(pos, e);
				return;
			}
	    	
	    	try {
	    		int historyIndex = api.getHistoryLength();
	    		Object zEvesPara = api.getHistoryElement(historyIndex);
	    		// add result first, because that will be displayed in hover
	    		state.addPara(pos, historyIndex, term, zEvesPara, true);
	    		handleResult(pos, zEvesPara);
	    		checkCancelled();
//	    		handleResult(pos, "History index: " + historyIndex);
	    		
	    	} catch (ZEvesException e) {
	    		state.addPara(pos, -1, term, e.getMessage(), false);
	    		handleZEvesException(pos, e);
	    		return;
	    	}
    	
    	} finally {
        	markFinished(unfinishedAnn);
    	}
	}
    
    @Override
	protected void visitProofScriptHead(ProofScript term, Position pos) {
		
		Annotation unfinishedAnn = markUnfinished(pos);
		
    	String theoremName = getProofScriptName(term);
    	int proofStep = ZEvesFileState.PROOF_GOAL_STEP;
	    	
    	try {

    		// add result first, because that will be displayed in hover
    		int goalStepIndex = 1;
    		ZEvesOutput result = api.getGoalProofStep(theoremName, goalStepIndex);
    		state.addProofResult(pos, term, proofStep, goalStepIndex, result, true);
    		handleResult(pos, result);
    		checkCancelled();
//	    	boolean goalProved = api.getGoalProvedState(theoremName);
//	    	handleResult(pos, "Proved: " + goalProved);
    		
    	} catch (ZEvesException e) {
    		state.addProofResult(pos, term, proofStep, null, e.getMessage(), false);
    		handleZEvesException(pos, e);
    		return;
    	} finally {
        	markFinished(unfinishedAnn);
    	}
	}
	
    @Override
	protected boolean beforeProofScriptCommands(ProofScript term, Position pos) {
    	// ensure current script is the goal
		String theoremName = getProofScriptName(term);
		
    	try {
    		api.setCurrentGoalName(theoremName);
    		checkCancelled();
		} catch (ZEvesException e) {
			state.addProofResult(pos, term, ZEvesFileState.PROOF_GOAL_STEP, null, e.getMessage(), false);
			handleZEvesException(pos, e);
			return false;
		}
    	
    	return true;
	}

	@Override
	protected void visitProofScriptEnd(ProofScript term, Position pos) {
		
		Annotation unfinishedAnn = markUnfinished(pos);
		
		try {
			
			String theoremName = getProofScriptName(term);
		
			try {
				boolean goalProved = api.getGoalProvedState(theoremName);
				handleResult(pos, "Proved: " + goalProved);
				checkCancelled();
			} catch (ZEvesException e) {
				handleZEvesException(pos, e);
			}
			
		} finally {
			markFinished(unfinishedAnn);
		}
	}
    
    @Override
    protected void visitProofCommand(ProofScript script, ProofCommand command, Position pos) {
    	
    	// mark unfinished
    	Annotation unfinishedAnn = markUnfinished(pos);
    	
    	try {

    		String theoremName = getProofScriptName(script);
    		String commandContents = command.accept(zEvesXmlPrinter);
    		int proofStep = command.getProofStep().intValue();
    		
	    	try {
				ZEvesOutput output = api.sendProofCommand(commandContents);
				handleResult(pos, output);
				checkCancelled();
			} catch (ZEvesException e) {
				state.addProofResult(pos, script, proofStep, null, e.getMessage(), false);
				handleZEvesException(pos, e);
				return;
			}
	    	
	    	try {
	    		int stepIndex = api.getGoalProofLength(theoremName);
//	    		state.addPara(term, stepIndex);
	    		
	    		ZEvesOutput proofResult = api.getGoalProofStep(theoremName, stepIndex);
	    		// add result first, because that will be displayed in hover
	    		state.addProofResult(pos, script, proofStep, stepIndex, proofResult, true);
	    		handleResult(pos, proofResult);
	    		checkCancelled();
	    		
//	    		handleResult(pos, "Step index: " + stepIndex);
	    		
	    	} catch (ZEvesException e) {
	    		handleZEvesException(pos, e);
	    		return;
	    	}
    	
    	} finally {
        	markFinished(unfinishedAnn);
    	}
    	
    }
    
    private String getProofScriptName(ProofScript script) {
    	return script.getName().accept(zEvesXmlPrinter);
    }
    
    private Annotation markUnfinished(Position pos) {
    	
    	if (annotations == null) {
    		return null;
    	}
    	
    	Annotation ann = annotations.addAnnotation(pos, ZEvesAnnotations.ANNOTATION_UNFINISHED);
    	
    	updateUnprocessed(getEnd(pos));
    	
    	tryFlush();
    	return ann;
    }
    
    private void markFinished(Annotation unfinishedAnn) {
    	
    	if (annotations == null || unfinishedAnn == null) {
    		return;
    	}
    	
    	annotations.removeAnnotation(unfinishedAnn);
//    	tryFlush();
    }

    private Object handleZEvesException(Position pos, ZEvesException e) {
    	
    	// TODO clear previous markers?
    	
    	boolean addedMarkers = false;
		if (annotations != null) {
			try {
				annotations.createErrorMarker(pos, e.getMessage());
				annotations.addAnnotation(pos, ZEvesAnnotations.ANNOTATION_FAILED);
				addedMarkers = true;
			} catch (CoreException ce) {
				ZEvesPlugin.getDefault().log(ce);
			}
			
//			tryFlush();
		}
		
		if (!addedMarkers) {
			// mark into log
			ZEvesPlugin.getDefault().log(e);
		}
		
		Throwable cause = e.getCause();
		if (cause != null) {
			// log the cause
			ZEvesPlugin.getDefault().log(cause);
		}
		
		return null;
    }
    
    private void handleResult(Position pos, Object result) {
    	
    	if (result == null) {
    		return;
    	}
    	
    	if ((result instanceof ZEvesOutput) && ((ZEvesOutput) result).isEmpty()) {
    		return;
    	}
    	
    	boolean warning = false;
    	String outStr;
		try {
			outStr = printResult(result);
		} catch (ZEvesException e) {
			warning = true; 
			outStr = e.getMessage();
		}
    	
    	if (annotations != null) {
			try {
				if (outStr != null) {
					
					if (warning) {
						annotations.createErrorMarker(pos, outStr, IMarker.SEVERITY_WARNING);
					} else {
						annotations.createResultMarker(pos, outStr);
					}
				}
				annotations.addAnnotation(pos, ZEvesAnnotations.ANNOTATION_FINISHED);
			} catch (CoreException ce) {
				ZEvesPlugin.getDefault().log(ce);
			}
			
//			tryFlush();
		}
    }

	private String printResult(Object result) throws ZEvesException {
		if (!(result instanceof ZEvesOutput)) {
//			return result.toString();
			return null;
		}
		
		// instead of printing everything, just get the actual results (e.g. proof goal) here
		Object firstResult = ((ZEvesOutput) result).getFirstResult();
		if (firstResult == null) {
			return null;
		}

		ZSect sect = getCurrentSect();
		String sectName = sect != null ? sect.getName() : null;
		
		String resultZEves = firstResult.toString();
		
		try {
			return ZEvesResultConverter.convertPred(sectInfo, sectName, resultZEves, Markup.UNICODE, 80);
		} catch (IOException e) {
			ZEvesPlugin.getDefault().log(e);
			throw handleParseException("I/O problems parsing Z/Eves result: " + e.getMessage(), e, resultZEves);
		} catch (CommandException e) {
			// TODO log this exception as well?
			Throwable cause = e.getCause();
			if (cause == null) {
				cause = e;
			}
			throw handleParseException("Cannot parse Z/Eves result: " + cause.getMessage(), cause, resultZEves);
		}
	}
	
	private ZEvesException handleParseException(String message, Throwable ex, String unparsedResult) {
		return new ZEvesException(message + "\nZ/Eves result:\n" + unparsedResult, ex);
	}

    private void updateUnprocessed(int newOffset) {
    	if (annotations != null) {
    		
    		if (unprocessedAnn != null) {
    			annotations.removeAnnotation(unprocessedAnn);
    		}
    		
    		int length = getEndOffset() - newOffset;
    		if (length > 0) { 
	    		unprocessedAnn = annotations.addAnnotation(
	    				new Position(newOffset, getEndOffset() - newOffset), 
	    				ZEvesAnnotations.ANNOTATION_UNPROCESSED);
    		}
    	}
    }
    
    private void tryFlush() {
    	
    	if (System.currentTimeMillis() - lastFlush > FLUSH_INTERVAL) {
    		flush();
    	}
    }
    
    public void flush() {
    	if (annotations != null) {
    		annotations.flushPendingMarkers();
    		annotations.flushPendingAnnotations();
    	}
    	
    	lastFlush = System.currentTimeMillis();
    }
    
    public void finish() {
    	// remove unprocessed annotation
    	if (annotations != null && unprocessedAnn != null) {
			annotations.removeAnnotation(unprocessedAnn);
    	}
    	
    	// flush annotations
    	flush();
    }
    
    private void checkCancelled() {
    	if (progressMonitor.isCanceled()) {
    		throw new CancelException();
    	}
    }
    
    public static class CancelException extends RuntimeException {}
    
}
