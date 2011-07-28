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
import net.sourceforge.czt.zeves.response.ZEvesOutput;

public class ZEvesFileState {

	public static final int PROOF_GOAL_STEP = -1;
	
	private final Map<Para, Object> paraResults = new HashMap<Para, Object>();
	
	private final List<ParaPosition> paraPositions = new ArrayList<ParaPosition>();
	private final List<ProofStepPosition> proofPositions = new ArrayList<ProofStepPosition>();
	
	private final Map<ProofStepId, ZEvesOutput> proofStepResults = new HashMap<ProofStepId, ZEvesOutput>();

	public void addPara(Position pos, int historyIndex) {
		
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
	
	public void addParaResult(Para para, Object result) {
		paraResults.put(para, result);
	}
	
	public Object getParaResult(Para para) {
		return paraResults.get(para);
	}
	
	public void addProofResult(Position pos, ProofScript script, int proofStep, ZEvesOutput result) {
		proofStepResults.put(new ProofStepId(script, proofStep), result);
		
		if (pos != null) {
			
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
	}
	
	public int getLastPositionOffset() {
		
		Position lastPara = getLastPosition(paraPositions);
		Position lastProof = getLastPosition(proofPositions);
		
		if (lastPara == null) {
			return getEnd(lastProof);
		}
		
		if (lastProof == null) {
			return getEnd(lastPara);
		}
		
		int paraEnd = getEnd(lastPara);
		int proofEnd = getEnd(lastProof);
		
		return paraEnd >= proofEnd ? paraEnd : proofEnd;
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
	
	public ZEvesOutput getProofResult(ProofScript script, int proofStep) {
		return proofStepResults.get(new ProofStepId(script, proofStep));
	}
	
	public void clear() {
		paraResults.clear();
		paraPositions.clear();
		proofPositions.clear();
		proofStepResults.clear();
	}
	
	public void undoThrough(ZEvesApi zEvesApi, Position pos) throws ZEvesException {
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
		
		System.out.println("Undo through history: " + undoThroughHistoryIndex);
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
			
			ProofScript script = proofPos.getScript();
			int proofStep = proofPos.getProofStep();
			String goalName = script.getZName().getWord();
			
			// increment undo count
			Integer undoCount = proofUndoCounts.get(goalName);
			proofUndoCounts.put(goalName, (undoCount != null ? undoCount.intValue() : 0) + 1);
			
			// remove from list and results map
			it.remove();
			proofStepResults.remove(new ProofStepId(script, proofStep));
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
	
	private boolean beforePos(PositionInfo info, Position pos) {
		Position iPos = info.getPosition();
		
		int infoEnd = iPos.getOffset() + iPos.getLength();
		return infoEnd < pos.getOffset();
	}
	
	private static class ProofStepId {
		private final ProofScript script;
		private final int proofStep;
		
		public ProofStepId(ProofScript script, int proofStep) {
			this.script = script;
			this.proofStep = proofStep;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + proofStep;
			result = prime * result + ((script == null) ? 0 : script.hashCode());
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
			if (script == null) {
				if (other.script != null)
					return false;
			} else if (!script.equals(other.script))
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
		
		private final ProofScript script;
		private final int proofStep;
		
		public ProofStepPosition(Position pos, ProofScript script, int proofStep) {
			super(pos);
			this.script = script;
			this.proofStep = proofStep;
		}
		
		public ProofScript getScript() {
			return script;
		}

		public int getProofStep() {
			return proofStep;
		}
	}
	
}
