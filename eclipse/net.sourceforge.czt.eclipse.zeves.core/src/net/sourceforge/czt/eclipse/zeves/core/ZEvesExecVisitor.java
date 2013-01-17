package net.sourceforge.czt.eclipse.zeves.core;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;

import org.apache.commons.lang.StringUtils;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.core.document.DocumentUtil;
import net.sourceforge.czt.eclipse.core.document.IPositionProvider;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecContext.ZEvesMessageType;
import net.sourceforge.czt.eclipse.zeves.core.ZEvesExecContext.ZEvesStatus;
import net.sourceforge.czt.eclipse.zeves.core.internal.ZEvesCorePlugin;
import net.sourceforge.czt.parser.util.SectParentResolver;
import net.sourceforge.czt.parser.util.SectParentResolver.CyclicSectionsException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.text.Position;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.proof.ZEvesTactics;
import net.sourceforge.czt.zeves.proof.ZEvesTactics.CommandSequence;
import net.sourceforge.czt.zeves.proof.ZEvesTactics.IgnorableCommand;
import net.sourceforge.czt.zeves.response.ZEvesError;
import net.sourceforge.czt.zeves.response.ZEvesOutput;
import net.sourceforge.czt.zeves.response.ZEvesError.ZEvesErrorType;
import net.sourceforge.czt.zeves.response.form.ZEvesName;
import net.sourceforge.czt.zeves.snapshot.SnapshotData;
import net.sourceforge.czt.zeves.snapshot.ZEvesSnapshot;
import net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter;

//import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.ZSECTION_BEGIN_PATTERN;
//import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.ZSECTION_END_PATTERN;
//import static net.sourceforge.czt.zeves.z.CZT2ZEvesPrinter.getParents;
/**
 * Special visitor class to translate top-level Z terms. 
 * Each element in the returned list must be transmitted to the Z/EVES
 * server separately, in the given order.
 */
public class ZEvesExecVisitor extends ZEvesPosVisitor {
	
	private final CZT2ZEvesPrinter zEvesXmlPrinter;
	
	private final ZEvesApi api;
	private final ZEvesSnapshot snapshot;
	private final ZEvesExecContext execContext;
	
	private final String filePath;
	private final SectionManager sectInfo;
	
	private Position unprocessedPos;
	
	private final IProgressMonitor progressMonitor;
	
	public ZEvesExecVisitor(ZEvesApi api, ZEvesSnapshot snapshot, ZEvesExecContext execContext,
			String filePath, SectionManager sectInfo, 
			int startOffset, int endOffset, IProgressMonitor progressMonitor) {
    	
		super(execContext.getTermPositions(filePath), startOffset, endOffset);
		this.api = api;
		this.snapshot = snapshot;
		this.execContext = execContext;
		
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
    	
    	markUnfinished(position);
		
		try {
			
			// if any parent errors happen, we will need to report them after "updatingSection" call
			ZEvesException parentEx = null;
			Parent errParent = null;
			
			for (Parent parent : term.getParent()) {
				
				try {
					// check for cyclic parents - we cannot submit recursively if the parents are cyclic
					SectParentResolver.checkCyclicParents(parent.getWord(), sectInfo);
				} catch (CommandException e) {
					// problems checking the parents
					parentEx = new ZEvesException("Problems checking for cyclic parents: " + e.getMessage(), e);
					break;
				} catch (CyclicSectionsException e) {
					parentEx = new ZEvesException(e.getMessage(), e);
					break;
				}
				
				// go recursively into parents
				parentEx = visitParent(parent);
				if (parentEx != null) {
					// problem in submitting the parent
					// do not continue to other parents, as it will mess up the order
					errParent = parent;
					break;
				}
				
				checkCancelled();
			}
			
			checkCancelled();
			
			if (parentEx != null) {
				// error in parent - use it as the section header result
				snapshot.updatingSectionError(position, filePath, getCurrentSectionName(),
						sectInfo, new SnapshotData.Builder(errParent).result(parentEx).build());
				handleZEvesException(position, term, parentEx);
			} else {
				snapshot.updatingSection(position, filePath, getCurrentSectionName(), sectInfo);
				handleResult(position, null);
			}
			
			checkCancelled();
			
			// Currently commented, because begin-section is unimplemented in Z/EVES
//    		String sectionBeginXml = MessageFormat.format(ZSECTION_BEGIN_PATTERN, term.getName(), getParents(term.getParent()));
//    		api.send(sectionBeginXml);
//    		checkCancelled();
//    	} catch (ZEvesException e) {
//    		// do not return - just handle and continue into paragraphs
//    		handleZEvesException(position, e);
    	} finally {
    		markFinished(position);
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
		
		markUnfinished(position);
		
		try {
			snapshot.completeSection(position, filePath, getCurrentSectionName());
			handleResult(position, null);
			checkCancelled();
			
			// Currently commented, because end-section is unimplemented in Z/EVES
//    		api.send(ZSECTION_END_PATTERN);
//    		checkCancelled();
//    	} catch (ZEvesException e) {
//    		handleZEvesException(position, e);
    	} finally {
    		markFinished(position);
    	}
	}

	public ZEvesException visitParent(Parent term) {
    	
    	String parentSectName = term.getWord();
    	
    	for (Section systemSection : Section.values()) {
    		if (systemSection == Section.ANONYMOUS) {
    			// do not ignore anonymous section?
    			continue;
    		}
    		
    		if (systemSection.getName().equals(parentSectName)) {
    			// system section - do not submit to Z/EVES
    			return null;
    		}
    	}
    	
    	try {
    		
	    	Source parentSource = sectInfo.get(new Key<Source>(parentSectName, Source.class));
	    	String parentFilePath = DocumentUtil.getPath(parentSource);
	    	
	    	if (parentFilePath == null) {
	    		// cannot find the file path
	    		// TODO report unsupported
	    	}
	    	
	    	ZSect parentSect = sectInfo.get(new Key<ZSect>(parentSectName, ZSect.class));
	    	
	    	if (snapshot.isSectionCompleted(parentFilePath, parentSect.getName())) {
	    		// section already submitted and completed
	    		return null;
	    	}
	    	
	    	IPositionProvider<? super Term> parentPosProvider = 
	    	    execContext.getTermPositions(parentFilePath);
	    	
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
	    	int endOffset = parentSectPos.getEndOffset() + 1;
	    	
	    	if (startOffset > endOffset) {
	    		/*
				 * This can happen if the parsed data is not synced between
				 * different sections. For example, if a parent changes (and
				 * submits to Z/EVES) but the section does not reparse - it
				 * still has old parsed info about the parent
				 */
				ZEvesException parentSyncEx = new ZEvesException(
						  "The parent " + parentSectName
						+ " is not synchronized with this section. "
						+ "It may have changed and section" + getCurrentSectionName()
						+ " needs to be parsed again.");
				
				return parentSyncEx;
	    	}
	    	
	    	ZEvesExecVisitor parentExec = new ZEvesExecVisitor(
	    			api, snapshot, execContext, 
	    			parentFilePath, sectInfo, 
	    			startOffset, endOffset, progressMonitor);
	    	
	    	try {
	    		// submit the parent section
	    		parentSect.accept(parentExec);
	    	} finally {
	    		parentExec.finish();
	    	}
			
    	} catch (CommandException ex) {
    		// TODO report the exception on the parent?
    		ZEvesCorePlugin.getDefault().log(ex);
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
    	markUnfinished(pos);
    	
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
        	markFinished(pos);
    	}
	}
    
    @Override
	protected void visitProofScriptHead(ProofScript term, Position pos) {
		
    	markUnfinished(pos);
		
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
        	markFinished(pos);
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
		
		pos = execContext.adaptFullLine(filePath, pos);
		markUnfinished(pos);
		
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
			markFinished(pos);
		}
	}
	
    @Override
    protected void visitProofCommand(ProofScript script, ProofCommand command, Position pos) {
    	
    	// mark unfinished
    	markUnfinished(pos);

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
						ZEvesCorePlugin.getDefault().log(e);
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
        	markFinished(pos);
    	}
    	
    }

    private boolean isNoEffectError(ZEvesException e) {
		return e.getZEvesError() != null
				&& e.getZEvesError().getType().contains(ZEvesErrorType.NO_EFFECT);
    }
    
    private String getProofScriptName(ProofScript script) {
    	return script.getName().accept(getZEvesXmlPrinter());
    }
    
  private void markUnfinished(Position pos)
  {
    execContext.addStatus(filePath, pos, ZEvesStatus.UNFINISHED);
    updateUnprocessed(pos.getEndOffset());
  }

  private void markFinished(Position pos)
  {
    execContext.removeStatus(filePath, pos, ZEvesStatus.UNFINISHED);
  }
  
  private void updateUnprocessed(int newOffset)
  {
    execContext.removeStatus(filePath, unprocessedPos, ZEvesStatus.UNPROCESSED);

    int length = Math.max(0, getEndOffset() - newOffset);
    unprocessedPos = new Position(newOffset, length);
    if (length > 0) {
      execContext.addStatus(filePath, unprocessedPos, ZEvesStatus.UNPROCESSED);
    }
  }

  private void handleZEvesException(Position pos, Term term, ZEvesException e)
  {

    boolean errAdded = execContext.addMessage(filePath, pos, e.getMessage(), ZEvesMessageType.ERROR);
    execContext.addStatus(filePath, pos, ZEvesStatus.FAILED);

    if (!errAdded || logDebug(e)) {
      // mark into log
      ZEvesCorePlugin.getDefault().log(e);
    }
  }

  private boolean logDebug(ZEvesException e)
  {
    // if there was an underlying cause, log it.
    // log Z/EVES parser, scanner errors at the moment
    return e.getCause() != null || (e.getDebugInfo() != null && logZEvesError(e.getZEvesError()));
  }

  private boolean logZEvesError(ZEvesError error)
  {
    if (error == null) {
      return false;
    }

    EnumSet<ZEvesErrorType> type = error.getType();
    return type.contains(ZEvesErrorType.PARSE_ERR) || type.contains(ZEvesErrorType.SCAN_ERR);
  }

  private void handleResult(Position pos, Object result)
  {
    handleResult(pos, result, false);
  }

  private void handleResult(Position pos, Object result, boolean resultTrue)
  {
    execContext.addStatus(filePath, pos, ZEvesStatus.FINISHED);

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
    }
    catch (ZEvesException e) {
      warning = true;
      outStr = e.getMessage();
    }

    if (outStr != null) {

      if (warning) {
        execContext.addMessage(filePath, pos, outStr, ZEvesMessageType.WARNING);
      }
      else {
        if (resultTrue) {
          execContext.addMessage(filePath, pos, outStr, ZEvesMessageType.RESULT_TRUE);
        }
        else {
          execContext.addMessage(filePath, pos, outStr, ZEvesMessageType.RESULT);
        }
      }
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
			ZEvesCorePlugin.getDefault().log(e);
			throw handleParseException("I/O problems parsing Z/EVES result: " + e.getMessage(), e, resultZEves);
		} catch (CommandException e) {
			// TODO log this exception as well?
			Throwable cause = e.getCause();
			if (cause == null) {
				cause = e;
			}
			throw handleParseException("Cannot parse Z/EVES result: " + StringUtils.strip(cause.getMessage()), 
					cause, resultZEves);
		}
	}
	
	private ZEvesException handleParseException(String message, Throwable ex, String unparsedResult) {
		return new ZEvesException(message + "\nZ/EVES result:\n" + unparsedResult, ex);
	}

  public void finish()
  {
    // remove unprocessed marker
    execContext.removeStatus(filePath, unprocessedPos, ZEvesStatus.UNPROCESSED);
    // mark completed to the exec context
    execContext.completed(filePath);
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
