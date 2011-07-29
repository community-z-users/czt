package net.sourceforge.czt.eclipse.zeves;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.jface.text.Position;

import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofScript;

import static java.lang.Math.max;

public class ZEvesFileState {

	public static final int PROOF_GOAL_STEP = -1;
	
	private final Map<Para, Object> paraResults = new HashMap<Para, Object>();
	
	private final List<ParaPosition> paraPositions = new ArrayList<ParaPosition>();
	private final List<ProofStepPosition> proofPositions = new ArrayList<ProofStepPosition>();
	private final List<Position> errorPositions = new ArrayList<Position>();
	
	private final Map<ProofStepId, Object> proofStepResults = new HashMap<ProofStepId, Object>();

	public void addPara(Position pos, int historyIndex, Para para, Object result, boolean success) {

		paraResults.put(para, result);
		
		if (success) {
			markParaSubmitted(pos, historyIndex);
		} else {
			markSubmitError(pos);
		}
	}

	private void markParaSubmitted(Position pos, int historyIndex) {
		// sanity check
		ParaPosition lastPos = getLastPosInfo(paraPositions);
		if (lastPos != null) {
			if (!beforePos(lastPos, pos)) {
				throw new IllegalArgumentException(
						"Paragraph positions must be added in increasing order. " +
						"Last position: [" + lastPos.getPosition() + "], new: [" + pos + "]");
			}
			
			if (lastPos.getHistoryIndex() >= historyIndex) {
				throw new IllegalArgumentException(
						"Paragraph history must be added in increasing order. " +
						"Last index: [" + lastPos.getHistoryIndex() + "], new: [" + historyIndex + "]");
			}
		}
		
		paraPositions.add(new ParaPosition(pos, historyIndex));
	}
	
	private void markSubmitError(Position pos) {
		
		// sanity check
		Position lastPos = getLastErrorPos();
		if (lastPos != null) {
			if (lastPos.getOffset() > pos.getOffset()) {
				throw new IllegalArgumentException(
						"Error positions must be added in increasing order. " +
						"Last position: [" + lastPos + "], new: [" + pos + "]");
			}
		}
		
		errorPositions.add(pos);
	}
	
	public Object getParaResult(Para para) {
		return paraResults.get(para);
	}
	
	public void addProofResult(Position pos, ProofScript script, int proofStep, Object result,
			boolean success) {
		String scriptName = getScriptName(script);
		proofStepResults.put(new ProofStepId(scriptName, proofStep), result);
		
		if (success) {
			// do not submit "goals"
			if (proofStep != PROOF_GOAL_STEP) {
				markProofSubmitted(pos, scriptName, proofStep);
			}
		} else {
			markSubmitError(pos);
		}
	}

	private void markProofSubmitted(Position pos, String script, int proofStep) {
		// sanity check
		ProofStepPosition lastPos = getLastPosInfo(proofPositions);
		if (lastPos != null) {
			if (!beforePos(lastPos, pos)) {
				throw new IllegalArgumentException(
						"Proof step positions must be added in increasing order. " +
						"Last position: [" + lastPos.getPosition() + "], new: [" + pos + "]");
			}
		}
		
		proofPositions.add(new ProofStepPosition(pos, script, proofStep));
	}
	
	public int getLastPositionOffset() {
		
		int paraEnd = getEnd(getLastPosition(paraPositions));
		int proofEnd = getEnd(getLastPosition(proofPositions));
		int errEnd = getEnd(getLastErrorPos());
		
		return max(max(paraEnd, proofEnd), errEnd);
	}
	
	private int getEnd(Position pos) {
		
		if (pos == null) {
			return -1;
		}
		
		return pos.getOffset() + pos.getLength();
	}
	
	private Position getLastPosition(List<? extends PositionInfo> list) {
		
		PositionInfo lastPos = getLastPosInfo(list);
		if (lastPos == null) {
			return null;
		}
		
		return lastPos.getPosition();
	}
	
	private <T extends PositionInfo> T getLastPosInfo(List<? extends T> list) {
		if (list.isEmpty()) {
			return null;
		}
		
		return list.get(list.size() - 1);
	}
	
	private Position getLastErrorPos() {
		if (errorPositions.isEmpty()) {
			return null;
		}
		
		return errorPositions.get(errorPositions.size() - 1);
	}
	
	public Object getProofResult(ProofScript script, int proofStep) {
		return proofStepResults.get(new ProofStepId(getScriptName(script), proofStep));
	}
	
	public void clear() {
		paraResults.clear();
		paraPositions.clear();
		proofPositions.clear();
		proofStepResults.clear();
		errorPositions.clear();
	}
	
	public void undoThrough(ZEvesApi zEvesApi, Position pos) throws ZEvesException {
		undoErrorsThrough(pos);
		undoProofsThrough(zEvesApi, pos);
		undoParaThrough(zEvesApi, pos);
	}

	private void undoParaThrough(ZEvesApi zEvesApi, Position pos) throws ZEvesException {
		
		int undoThroughHistoryIndex = -1;
		
		List<ParaPosition> retained = new ArrayList<ParaPosition>();
		
		for (ParaPosition paraPos : paraPositions) {
			if (!beforePos(paraPos, pos)) {
				undoThroughHistoryIndex = paraPos.getHistoryIndex();
				break;
			} else {
				retained.add(paraPos);
			}
		}
		
		if (undoThroughHistoryIndex > 0) {
			paraPositions.clear();
			paraPositions.addAll(retained);
			
			zEvesApi.undoBackThrough(undoThroughHistoryIndex);
		}
	}
	
	private void undoProofsThrough(ZEvesApi zEvesApi, Position pos) throws ZEvesException {
		
		Map<String, Integer> proofUndoCounts = new HashMap<String, Integer>();
		
		boolean removing = false;
		for (Iterator<ProofStepPosition> it = proofPositions.iterator(); it.hasNext(); ) {
			
			ProofStepPosition proofPos = it.next();
			if (!removing && beforePos(proofPos, pos)) {
				// still before the position
				continue;
			}

			// removing - mark for 'back' and remove from list as well as results map
			removing = true;
			
			String goalName = proofPos.getScriptName();
			int proofStep = proofPos.getProofStep();
			
			// increment undo count
			Integer undoCount = proofUndoCounts.get(goalName);
			proofUndoCounts.put(goalName, (undoCount != null ? undoCount.intValue() : 0) + 1);
			
			// remove from list and results map
			it.remove();
			proofStepResults.remove(new ProofStepId(goalName, proofStep));
		}
		
		if (proofUndoCounts.isEmpty()) {
			return;
		}
		
		for (Entry<String, Integer> countEntry : proofUndoCounts.entrySet()) {
			String goalName = countEntry.getKey();
			int undoCount = countEntry.getValue();
			
			zEvesApi.setCurrentGoalName(goalName);
			zEvesApi.back(undoCount);
		}
	}
	
	private String getScriptName(ProofScript script) {
		return script.getZName().getWord(); 
	}
	
	private void undoErrorsThrough(Position pos) {
		
		for (Iterator<Position> it = errorPositions.iterator(); it.hasNext(); ) {
			
			Position errPos = it.next();
			if (!beforePos(errPos, pos)) {
				it.remove();
			}
		}
	}
	
	private boolean beforePos(PositionInfo info, Position pos) {
		return beforePos(info.getPosition(), pos);
	}
	
	private boolean beforePos(Position elemPos, Position pos) {
		int elemEnd = elemPos.getOffset() + elemPos.getLength();
		return elemEnd < pos.getOffset();
	}

	// TODO proof scripts with the same name?
	private static class ProofStepId {
		private final String scriptName;
		private final int proofStep;
		
		public ProofStepId(String scriptName, int proofStep) {
			this.scriptName = scriptName;
			this.proofStep = proofStep;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + proofStep;
			result = prime * result + ((scriptName == null) ? 0 : scriptName.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			ProofStepId other = (ProofStepId) obj;
			if (proofStep != other.proofStep)
				return false;
			if (scriptName == null) {
				if (other.scriptName != null)
					return false;
			} else if (!scriptName.equals(other.scriptName))
				return false;
			return true;
		}

	}
	
	private abstract class PositionInfo {
		
		private final Position pos;
		
		public PositionInfo(Position pos) {
			this.pos = pos;
		}
		
		public Position getPosition() {
			return pos;
		}
	}
	
	private class ParaPosition extends PositionInfo {
		
		private final int historyIndex;
		
		public ParaPosition(Position pos, int historyIndex) {
			super(pos);
			this.historyIndex = historyIndex;
		}
		
		public int getHistoryIndex() {
			return historyIndex;
		}
	}
	
	private class ProofStepPosition extends PositionInfo {
		
		private final String script;
		private final int proofStep;
		
		public ProofStepPosition(Position pos, String script, int proofStep) {
			super(pos);
			this.script = script;
			this.proofStep = proofStep;
		}
		
		public String getScriptName() {
			return script;
		}

		public int getProofStep() {
			return proofStep;
		}
	}
	
}
