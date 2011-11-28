package net.sourceforge.czt.eclipse.zeves.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;

import org.apache.commons.lang.StringUtils;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.parser.IPositionProvider;
import net.sourceforge.czt.eclipse.editors.parser.TermPositionProvider;
import net.sourceforge.czt.eclipse.zeves.ZEvesPlugin;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesMarkers.MarkerInfo;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesTactics.CommandSequence;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesTactics.IgnorableCommand;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Section;
import net.sourceforge.czt.z.visitor.ParentVisitor;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesError;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesError.ZEvesErrorType;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

//import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.ZSECTION_BEGIN_PATTERN;
//import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.ZSECTION_END_PATTERN;
//import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.getParents;

/**
 * Special visitor class to translate top-level Z terms. 
 * Each element in the returned list must be transmitted to the Z/Eves
 * server separately, in the given order.
 */
public class ZEvesExecVisitor extends ZEvesPosVisitor implements ParentVisitor<Object> {
	
	private final CZT2ZEvesPrinter zEvesXmlPrinter;
	
	private final ZEvesApi api;
	private final ZEvesSnapshot snapshot;
	private final ZEvesMarkers markers;
	private final IDocument document;
	
	private final String filePath;
	private final SectionManager sectInfo;
	
	private MarkerInfo unprocessedMarker;
	
	private final IProgressMonitor progressMonitor;
	
	private static final long FLUSH_INTERVAL = 500;
	private long lastFlush = 0;
	
	public ZEvesExecVisitor(ZEvesApi api, ZEvesSnapshot snapshot, ZEvesMarkers markers, IDocument document,
			String filePath, IPositionProvider<? super Term> posProvider, SectionManager sectInfo, 
			int startOffset, int endOffset, IProgressMonitor progressMonitor) {
    	
		super(posProvider, startOffset, endOffset);
		this.api = api;
		this.snapshot = snapshot;
		this.markers = markers;
		this.document = document;
		
		this.filePath = filePath;
		this.sectInfo = sectInfo;
		this.zEvesXmlPrinter = new CZT2ZEvesPrinter(sectInfo);
		
		if (progressMonitor == null) {
			progressMonitor = new NullProgressMonitor();
		}
		
		this.progressMonitor = progressMonitor;
	}
	
    @Override
	protected void visitZSectHead(ZSect term, Position position) {
    	
    	MarkerInfo unfinishedMarker = markUnfinished(position);
		
		try {
			
			for (Parent parent : term.getParent()) {
				parent.accept(this);
				checkCancelled();
			}
			
			snapshot.updatingSection(position, filePath, getCurrentSectionName(), sectInfo);
			handleResult(position, null);
			checkCancelled();
			
			// Currently commented, because begin-section is unimplemented in Z/Eves
//    		String sectionBeginXml = MessageFormat.format(ZSECTION_BEGIN_PATTERN, term.getName(), getParents(term.getParent()));
//    		api.send(sectionBeginXml);
//    		checkCancelled();
//    	} catch (ZEvesException e) {
//    		// do not return - just handle and continue into paragraphs
//    		handleZEvesException(position, e);
    	} finally {
    		markFinished(unfinishedMarker);
    	}
		
	}

	@Override
	protected void beforeZSectParas(ZSect term, Position pos) {
		// mark the section as updating in the snapshot
		// no need to pass in the position here - it should have been passed
		// during section head visit
		snapshot.updatingSection(null, filePath, getCurrentSectionName(), sectInfo);
	}

	@Override
	protected void visitZSectEnd(ZSect term, Position position) {
		
		MarkerInfo unfinishedMarker = markUnfinished(position);
		
		try {
			snapshot.completeSection(position, filePath, getCurrentSectionName());
			handleResult(position, null);
			checkCancelled();
			
			// Currently commented, because end-section is unimplemented in Z/Eves
//    		api.send(ZSECTION_END_PATTERN);
//    		checkCancelled();
//    	} catch (ZEvesException e) {
//    		handleZEvesException(position, e);
    	} finally {
    		markFinished(unfinishedMarker);
    	}
	}

    @Override
	public Object visitParent(Parent term) {
    	
    	String parentSectName = term.getWord();
    	
    	for (Section systemSection : Section.values()) {
    		if (systemSection == Section.ANONYMOUS) {
    			// do not ignore anonymous section?
    			continue;
    		}
    		
    		if (systemSection.getName().equals(parentSectName)) {
    			// system section - do not submit to Z/Eves
    			return null;
    		}
    	}
    	
    	try {
    		
	    	Source parentSource = sectInfo.get(new Key<Source>(parentSectName, Source.class));
	    	if (!(parentSource instanceof FileSource)) {
	    		// TODO report unsupported
	    		return null;
	    	}
	    	
	    	String parentFilePath = parentSource.getName();
	    	
	    	ZSect parentSect = sectInfo.get(new Key<ZSect>(parentSectName, ZSect.class));
	    	
	    	if (snapshot.isSectionCompleted(parentFilePath, parentSect.getName())) {
	    		// section already submitted and completed
	    		return null;
	    	}
	    	
	    	// TODO resolve parent loops somehow?
	    	
	    	IFile parentResource = null;
	    	List<IFile> files = ResourceUtil.findFile(parentFilePath);
	    	if (files.size() > 0) {
	    		// take the first one found
	    		// TODO support multiple resources (e.g. the same file is several times in the workspace)?
	    		parentResource = files.get(0);
	    	}
	    	
	    	IDocument parentDocument = null;
	    	if (parentResource != null) {
	    		TextFileDocumentProvider documentProvider = new TextFileDocumentProvider();
	    		try {
					documentProvider.connect(parentResource);
					parentDocument = documentProvider.getDocument(parentResource);
				} catch (CoreException e) {
					// ignore?
					ZEvesPlugin.getDefault().log(e);
				}
	    	}
	    	
	    	ZEvesMarkers parentAnns = parentResource != null ? 
	    			new ZEvesMarkers(parentResource, parentDocument) : null;
	    	IPositionProvider<Term> parentPosProvider = new TermPositionProvider(parentDocument);
	    	
	    	Position parentSectPos = parentPosProvider.getPosition(parentSect);

	    	// check how much (possibly) parent has already been submitted
	    	int parentSubmitOffset = snapshot.getLastPositionOffset(parentFilePath);
	    	int startOffset;
	    	if (parentSubmitOffset >= 0) {
	    		// start from the next one
	    		startOffset = parentSubmitOffset + 1;
	    	} else {
	    		// get offsets from the section position
	    		startOffset = parentSectPos.getOffset();
	    	}
	    	
	    	// continue until the end of the section
	    	// note: add +1 to the end, otherwise "end section" is excluded
	    	int endOffset = getEnd(parentSectPos) + 1;
	    	
	    	ZEvesExecVisitor parentExec = new ZEvesExecVisitor(
	    			api, snapshot, parentAnns, parentDocument, 
	    			parentFilePath, parentPosProvider, sectInfo, 
	    			startOffset, endOffset, progressMonitor);
	    	
	    	try {
	    		// submit the parent section
	    		parentSect.accept(parentExec);
	    	} finally {
	    		parentExec.finish();
	    	}
			
    	} catch (CommandException ex) {
    		// TODO report the exception on the parent?
    		ZEvesPlugin.getDefault().log(ex);
    	}
    	
		return null;
	}

	@Override
	public Object visitLatexMarkupPara(LatexMarkupPara term) {
		// always visit Latex Markup paragraph to setup optemplate printing
		// TODO review whether to send the results
		term.accept(getZEvesXmlPrinter());
		return super.visitLatexMarkupPara(term);
	}

	@Override
	protected void visitPara(Para term, Position pos) {
    	// mark unfinished
    	MarkerInfo unfinishedMarker = markUnfinished(pos);
    	
    	SnapshotData.Builder dataBuilder = new SnapshotData.Builder(term);
    	
    	try {
    	
	    	String commandXml = term.accept(getZEvesXmlPrinter());
	
	    	try {
				ZEvesOutput output = api.send(commandXml);
				handleResult(pos, output);
				checkCancelled();
			} catch (ZEvesException e) {
				snapshot.addError(pos, dataBuilder.result(e).build());
				handleZEvesException(pos, term, e);
				return;
			}
	    	
	    	try {
	    		int historyIndex = api.getHistoryLength();
	    		Object zEvesPara = api.getHistoryElement(historyIndex);
	    		
	    		snapshot.addParaResult(pos, historyIndex, dataBuilder.result(zEvesPara).build());
	    		handleResult(pos, zEvesPara);
	    		checkCancelled();
	    		
	    	} catch (ZEvesException e) {
	    		snapshot.addError(pos, dataBuilder.result(e).build());
	    		handleZEvesException(pos, term, e);
	    		return;
	    	}
    	
    	} finally {
        	markFinished(unfinishedMarker);
    	}
	}
    
    @Override
	protected void visitProofScriptHead(ProofScript term, Position pos) {
		
    	MarkerInfo unfinishedMarker = markUnfinished(pos);
		
    	String theoremName = getProofScriptName(term);
    	
    	SnapshotData.Builder dataBuilder = new SnapshotData.Builder(term).goalName(theoremName).goal();
	    	
    	try {

    		// add result first, because that will be displayed in hover
    		ZEvesOutput result = api.getGoalProofStep(theoremName, ZEvesSnapshot.GOAL_STEP_INDEX);
    		
    		SnapshotData data = dataBuilder.result(result)
    									   .trace(Collections.singletonList(result))
    									   .build();
    		
    		snapshot.addGoalResult(pos, theoremName, data);
    		
    		handleResult(pos, result);
    		checkCancelled();
//	    	boolean goalProved = api.getGoalProvedState(theoremName);
//	    	handleResult(pos, "Proved: " + goalProved);
    		
    	} catch (ZEvesException e) {
    		handleZEvesException(pos, term, e);
//    		handleZEvesException1(pos, term, e, false);
    		return;
    	} finally {
        	markFinished(unfinishedMarker);
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
			snapshot.addError(pos, new SnapshotData
					.Builder(term)
					.goalName(theoremName)
					.goal()
					.result(e).build());
			handleZEvesException(pos, term, e);
			return false;
		}
    	
    	return true;
	}

	@Override
	protected void visitProofScriptEnd(ProofScript term, Position pos) {
		
		if (term.getProofCommandList().isEmpty()) {
			/*
			 * No proof commands - do not check goal state for empty proof
			 * script. This is also to accommodate lack of proper calculation of
			 * proof script head/end for empty script, which would throw an
			 * error otherwise.
			 */
			return;
		}
		
		pos = adaptFullLine(pos);
		MarkerInfo unfinishedMarker = markUnfinished(pos);
		
		try {
			
			String theoremName = getProofScriptName(term);
		
			try {
				boolean goalProved = api.getGoalProvedState(theoremName);
				if (!goalProved) {
					// do not display that goal is proved, instead just show an error otherwise,
					// i.e. if proof script end reached without having proved the goal
					ZEvesException unfinishedEx = new ZEvesException("Goal " + theoremName + " not proved");
					snapshot.addError(pos, new SnapshotData.Builder(term)
						.goalName(theoremName)
						.result(unfinishedEx).build());
					handleZEvesException(pos, term, unfinishedEx);
				}
				checkCancelled();
			} catch (ZEvesException e) {
				handleZEvesException(pos, term, e);
			}
			
		} finally {
			markFinished(unfinishedMarker);
		}
	}
	
	private Position adaptFullLine(Position pos) {

		if (document == null) {
			return pos;
		}
		
		try {
			int line = document.getLineOfOffset(pos.getOffset());
			int lineStart = document.getLineOffset(line);
			if (lineStart >= pos.getOffset()) {
				// already full line
				return pos;
			}
			
			// starting in the middle of the line - get the next line
			if (line < document.getNumberOfLines() - 1) {
				int nextLine = line + 1;
				int nextLineStart = document.getLineOffset(nextLine);
				int posEnd = getEnd(pos);
				if (nextLineStart <= posEnd) {
					return new Position(nextLineStart, posEnd - nextLineStart);
				}
			}
			
		} catch (BadLocationException e) {
			// ignore
		}
		
		// invalid - return previous
		return pos;
	}
    
    @Override
    protected void visitProofCommand(ProofScript script, ProofCommand command, Position pos) {
    	
    	// mark unfinished
    	MarkerInfo unfinishedMarker = markUnfinished(pos);

    	String theoremName = getProofScriptName(script);
    	
    	SnapshotData.Builder dataBuilder = new SnapshotData.Builder(command).goalName(theoremName);
    	
    	try {

    		/*
    		 * The command may be a tactic, represented by a command sequence,
    		 * thus resolve the command into a command sequence
    		 */
    		CommandSequence commandSeq = ZEvesTactics.getTacticCommands(command, getZEvesXmlPrinter());
    		Assert.isTrue(!commandSeq.getCommands().isEmpty());
    		
    		// command sequence may loop - it should be repeated until fixed point
    		// or until stopped by ineffective command
    		int loopCount = commandSeq.getLoopCount();

    		// capture the trace and last exception/step index
    		// we only need the last exception/step index for the snapshot
    		ZEvesException lastException = null;
    		int lastStepIndex = -1;
    		
    		// count submissions to backtrack correctly upon failure 
    		int submittedCount = 0;
    		List<ZEvesOutput> results = new ArrayList<ZEvesOutput>();
    		
    		// loop the indicated number of steps, or unlimited
    		for (int loop = 0; loop < loopCount || loopCount == CommandSequence.UNLIMITED; loop++) {
    			
    			boolean affected = false;
    			
	    		for (IgnorableCommand cmd : commandSeq.getCommands()) {
	    			
	    			String commandContents = cmd.getCommand();
	    			
	        		try {
	        			api.sendProofCommand(commandContents);
	        			submittedCount++;
	        			
	        			affected = true;
	        			
	        			int stepIndex = api.getGoalProofLength(theoremName);
	        			lastStepIndex = stepIndex;
				
	        			ZEvesOutput proofResult = api.getGoalProofStep(theoremName, stepIndex);
	        			results.add(proofResult);
	        			
					} catch (ZEvesException e) {
						lastException = e;

						if (isNoEffectError(e)) {
							
							// no effect from the command here
							if (cmd.isStopOnNoEffect()) {
								break;
							}
							
						} else {
							
							/*
							 * Unknown error - stop if needed.
							 * 
							 * Do not break on error by default, e.g. eq-subst.
							 * errors may report errors rectified by a
							 * subsequent rewrite call
							 */
							if (cmd.isStopOnError()) {
								break;
							}
						}
					}
	    		}
	    		
	    		if (!affected) {
	    			// the whole command list went without any effect,
	    			// thus a fixed point has been reached
	    			// break the loop
	    			// (this is in case none of the commands are "stop on no effect")
	    			break;
	    		}
	    		
    		}
    		
    		if (lastException != null && !isNoEffectError(lastException)) {
    			
    			// a serious error - handle the exception
    			snapshot.addError(pos, dataBuilder.result(lastException).build());
    			handleZEvesException(pos, command, lastException);
    			
    			if (submittedCount > 0) {
    				// something was submitted before the error, undo these steps
    				try {
						api.back(submittedCount);
					} catch (ZEvesException e) {
						// just log - we cannot handle half-state now..
						ZEvesPlugin.getDefault().log(e);
					}
    			}
    			
    			return;
    		}
    		
    		if (results.isEmpty()) {
    			// no results - report last exception (should be No change error)
    			snapshot.addError(pos, dataBuilder.result(lastException).build());
    			handleZEvesException(pos, command, lastException);
    			return;
    		}
    		
    		Assert.isTrue(results.size() == submittedCount);
    		
    		ZEvesOutput lastResult = results.get(results.size() - 1);
    		
    		snapshot.addProofResult(pos, theoremName, submittedCount, dataBuilder
    				.proofStep(lastStepIndex)
    				.result(lastResult)
    				.trace(results).build());
			
			handleResult(pos, lastResult, isResultTrue(lastResult));
			checkCancelled();
    		
    	
    	} finally {
        	markFinished(unfinishedMarker);
    	}
    	
    }

    private boolean isNoEffectError(ZEvesException e) {
		return e.getZEvesError() != null
				&& e.getZEvesError().getType().contains(ZEvesErrorType.NO_EFFECT);
    }
    
    private String getProofScriptName(ProofScript script) {
    	return script.getName().accept(getZEvesXmlPrinter());
    }
    
    private MarkerInfo markUnfinished(Position pos) {
    	
    	if (markers == null) {
    		return null;
    	}
    	
    	MarkerInfo marker = null;
		try {
			marker = markers.createStatusMarker(pos, ZEvesMarkers.STATUS_UNFINISHED);
		} catch (CoreException ce) {
			ZEvesPlugin.getDefault().log(ce);
		}
    	
    	updateUnprocessed(getEnd(pos));
    	
    	tryFlush();
    	return marker;
    }
    
    private void markFinished(MarkerInfo unfinishedMarker) {
    	
    	if (markers == null || unfinishedMarker == null) {
    		return;
    	}
    	
    	markers.deleteMarker(unfinishedMarker);
//    	tryFlush();
    }

    private void handleZEvesException(Position pos, Term term, ZEvesException e) {
    	
    	boolean addedMarkers = false;
		if (markers != null) {
			try {
				markers.createErrorMarker(pos, e.getMessage());
				markers.createStatusMarker(pos, ZEvesMarkers.STATUS_FAILED);
				addedMarkers = true;
			} catch (CoreException ce) {
				ZEvesPlugin.getDefault().log(ce);
			}
			
//			tryFlush();
		}
		
		if (!addedMarkers || logDebug(e)) {
			// mark into log
			ZEvesPlugin.getDefault().log(e);
		}
    }
    
    private boolean logDebug(ZEvesException e) {
    	// if there was an underlying cause, log it.
		return e.getCause() != null
				// log Z/Eves parser, scanner errors at the moment
				|| (e.getDebugInfo() != null && logZEvesError(e.getZEvesError()));
    }
    
    private boolean logZEvesError(ZEvesError error) {
    	if (error == null) {
    		return false;
    	}
    	
    	EnumSet<ZEvesErrorType> type = error.getType();
		return type.contains(ZEvesErrorType.PARSE_ERR) || type.contains(ZEvesErrorType.SCAN_ERR);
    }
    
    private void handleResult(Position pos, Object result) {
    	handleResult(pos, result, false);
    }
    
    private void handleResult(Position pos, Object result, boolean resultTrue) {
    	
    	if (markers != null) {
    		try {
				markers.createStatusMarker(pos, ZEvesMarkers.STATUS_FINISHED);
			} catch (CoreException ce) {
				ZEvesPlugin.getDefault().log(ce);
			}
    	}
    	
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
    	
    	if (markers != null) {
			try {
				if (outStr != null) {
					
					if (warning) {
						markers.createErrorMarker(pos, outStr, IMarker.SEVERITY_WARNING);
					} else {
						if (resultTrue) {
							markers.createResultTrueMarker(pos, outStr);
						} else {
							markers.createResultMarker(pos, outStr);
						}
					}
				}
//				markers.createStatusMarker(pos, ZEvesMarkers.STATUS_FINISHED);
			} catch (CoreException ce) {
				ZEvesPlugin.getDefault().log(ce);
			}
			
//			tryFlush();
		}
    }
    
    private boolean isResultTrue(ZEvesOutput result) {
    	if (result.getResults().size() == 1) {
    		// only one result, and it must be "true"
    		Object firstResult = result.getFirstResult();
    		if (firstResult instanceof ZEvesName) {
    			String value = ((ZEvesName) firstResult).getIdent();
    			return Boolean.valueOf(value);
    		}
    	}
    	
    	return false;
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
		
		String resultZEves = firstResult.toString().trim();
		
		if (ZEvesOutput.UNPRINTABLE_PREDICATE.equals(resultZEves)) {
			// a special case - do not try parsing
			return resultZEves;
		}

		ZSect sect = getCurrentSect();
		String sectName = sect != null ? sect.getName() : null;
		
		try {
			return ZEvesResultConverter.convertPred(sectInfo, sectName, resultZEves, Markup.UNICODE, 80, true);
		} catch (IOException e) {
			ZEvesPlugin.getDefault().log(e);
			throw handleParseException("I/O problems parsing Z/Eves result: " + e.getMessage(), e, resultZEves);
		} catch (CommandException e) {
			// TODO log this exception as well?
			Throwable cause = e.getCause();
			if (cause == null) {
				cause = e;
			}
			throw handleParseException("Cannot parse Z/Eves result: " + StringUtils.strip(cause.getMessage()), 
					cause, resultZEves);
		}
	}
	
	private ZEvesException handleParseException(String message, Throwable ex, String unparsedResult) {
		return new ZEvesException(message + "\nZ/Eves result:\n" + unparsedResult, ex);
	}

    private void updateUnprocessed(int newOffset) {
    	if (markers != null) {
    		
    		if (unprocessedMarker != null) {
    			markers.deleteMarker(unprocessedMarker);
    		}
    		
    		int length = getEndOffset() - newOffset;
    		if (length > 0) {
    			unprocessedMarker = null;
    			try {
		    		unprocessedMarker = markers.createProcessMarker(
		    				new Position(newOffset, getEndOffset() - newOffset));
    			} catch (CoreException ce) {
    				ZEvesPlugin.getDefault().log(ce);
    			}
    		}
    	}
    }
    
    private void tryFlush() {
    	
    	if (System.currentTimeMillis() - lastFlush > FLUSH_INTERVAL) {
    		flush();
    	}
    }
    
    public void flush() {
    	if (markers != null) {
    		markers.flushPendingMarkers();
    	}
    	
    	lastFlush = System.currentTimeMillis();
    }
    
    public void finish() {
    	// remove unprocessed marker
    	if (markers != null && unprocessedMarker != null) {
			markers.deleteMarker(unprocessedMarker);
    	}
    	
    	// flush marker
    	flush();
    }
    
    private void checkCancelled() {
    	if (progressMonitor.isCanceled()) {
    		throw new OperationCanceledException();
    	}
    }

	private CZT2ZEvesPrinter getZEvesXmlPrinter() {
		// synchronize current section name
		ZSect sect = getCurrentSect();
		String sectName = sect != null ? sect.getName() : null;
		zEvesXmlPrinter.setSectionName(sectName);
		
		return zEvesXmlPrinter;
	}
	
}
