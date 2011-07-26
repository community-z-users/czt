package net.sourceforge.czt.eclipse.zeves.editor;

import java.text.MessageFormat;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;

import net.sourceforge.czt.eclipse.zeves.ZEvesFileState;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
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
	private Annotation unprocessedAnn;
	
	private static final long FLUSH_INTERVAL = 500;
	private long lastFlush = 0;
	
    public ZEvesExecVisitor(ZEvesApi api, ZEvesFileState state, ZEvesAnnotations annotations,
    		int startOffset, int endOffset) {
    	
		super(startOffset, endOffset);
		this.api = api;
		this.state = state;
		this.annotations = annotations;
	}

    @Override
	protected void visitZSectHead(ZSect term, Position position) {
    	
    	Annotation unfinishedAnn = markUnfinished(position);
		
		try {
    		String sectionBeginXml = MessageFormat.format(ZSECTION_BEGIN_PATTERN, term.getName(), getParents(term.getParent()));
    		api.send(sectionBeginXml);
    	} catch (ZEvesException e) {
    		// do not return - just handle and continue into paragraphs
    		handleZEvesException(position, e);
    	}
		
		markFinished(unfinishedAnn);
	}

	@Override
	protected void visitZSectEnd(ZSect term, Position position) {
		
		Annotation unfinishedAnn = markUnfinished(position);
		
		try {
    		api.send(ZSECTION_END_PATTERN);
    	} catch (ZEvesException e) {
    		handleZEvesException(position, e);
    	}
		
		markFinished(unfinishedAnn);
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
			} catch (ZEvesException e) {
				handleZEvesException(pos, e);
				return;
			}
	    	
	    	try {
	    		int historyIndex = api.getHistoryLength();
	    		state.addPara(term, historyIndex);
	    		
	    		Object zEvesPara = api.getHistoryElement(historyIndex);
	    		// add result first, because that will be displayed in hover
	    		state.addParaResult(term, zEvesPara);
	    		handleResult(pos, zEvesPara);
	    		
//	    		handleResult(pos, "History index: " + historyIndex);
	    		
	    	} catch (ZEvesException e) {
	    		handleZEvesException(pos, e);
	    		return;
	    	}
    	
    	} finally {
        	markFinished(unfinishedAnn);
    	}
	}
    
    @Override
	protected boolean visitProofScriptHead(ProofScript term, Position pos) {
		
		Annotation unfinishedAnn = markUnfinished(pos);
		
    	try {
        	
    		String theoremName = getProofScriptName(term);
    		
	    	try {
	    		api.setCurrentGoalName(theoremName);
			} catch (ZEvesException e) {
				handleZEvesException(pos, e);
				return false;
			}
	    	
	    	try {
	
	    		// TODO add paragraph for proof script?
//	    		state.addPara(term, historyIndex);
	    		
	    		// add result first, because that will be displayed in hover
	    		ZEvesOutput result = api.getGoalProofStep(theoremName, 1);
//	    		state.addParaResult(term, zEvesPara);
	    		handleResult(pos, result);
	    		
//	    		boolean goalProved = api.getGoalProvedState(theoremName);
//	    		handleResult(pos, "Proved: " + goalProved);
	    		
	    	} catch (ZEvesException e) {
	    		handleZEvesException(pos, e);
	    		return false;
	    	}
	    	
    	} finally {
        	markFinished(unfinishedAnn);
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
    		
	    	try {
				ZEvesOutput output = api.sendCommand("proof-command", commandContents);
				handleResult(pos, output);
			} catch (ZEvesException e) {
				handleZEvesException(pos, e);
				return;
			}
	    	
	    	try {
	    		int stepIndex = api.getGoalProofLength(theoremName);
//	    		state.addPara(term, stepIndex);
	    		
	    		ZEvesOutput proofResult = api.getGoalProofStep(theoremName, stepIndex);
	    		// add result first, because that will be displayed in hover
	    		state.addProofResult(script, command.getProofStep().intValue(), proofResult);
	    		handleResult(pos, proofResult);
	    		
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
    	
//      // TODO ? need to sanitize the name, e.g. Z/Eves MySchema\$domainCheck - need to remove the backslash
//		theoremName = theoremName.replace("\\$", "$");
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
		
		return null;
    }
    
    private void handleResult(Position pos, Object result) {
    	
    	if (result == null) {
    		return;
    	}
    	
    	if ((result instanceof ZEvesOutput) && ((ZEvesOutput) result).isEmpty()) {
    		return;
    	}
    	
    	if (annotations != null) {
			try {
				annotations.createResultMarker(pos, result.toString());
				annotations.addAnnotation(pos, ZEvesAnnotations.ANNOTATION_FINISHED);
			} catch (CoreException ce) {
				ZEvesPlugin.getDefault().log(ce);
			}
			
//			tryFlush();
		}
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
    
}
