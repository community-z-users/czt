package net.sourceforge.czt.eclipse.zeves;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.AbstractMap.SimpleEntry;

import org.eclipse.jface.text.Position;

import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesOutput;

public class ZEvesFileState {
	
	private enum ResultType {
		PARA,
		GOAL,
		PROOF,
		ERROR
	}
	
	private static final PositionOverlapComparator POSITION_OVERLAP = new PositionOverlapComparator();

	private final List<Entry<PositionInfo, Object>> positionResults = new ArrayList<Entry<PositionInfo, Object>>();

	
	public void addParaResult(Position pos, int historyIndex, Object result) {

		checkPositionLegal(pos);
		
		// sanity check
		ParaPosition lastPos = (ParaPosition) getLastPositionInfo(ResultType.PARA);
		if (lastPos != null) {
			if (lastPos.getHistoryIndex() >= historyIndex) {
				throw new IllegalArgumentException(
						"Paragraph history must be added in increasing order. " +
						"Last index: [" + lastPos.getHistoryIndex() + "], new: [" + historyIndex + "]");
			}
		}
		
		addResult(new ParaPosition(pos, historyIndex), result);
	}
	
	private void addResult(PositionInfo posInfo, Object result) {
		positionResults.add(new SimpleEntry<PositionInfo, Object>(posInfo, result));
	}

	public void addError(Position pos, ZEvesException ex) {
		checkPositionLegal(pos);
		addResult(new PositionInfo(pos, ResultType.ERROR), ex);
	}
	
	private void checkPositionLegal(Position pos) {
		// sanity check
		Position lastPos = getLastPosition();
		if (lastPos != null) {
			if (lastPos.getOffset() > pos.getOffset()) {
				throw new IllegalArgumentException(
						"Result positions must be added in increasing order. " +
						"Last position: [" + lastPos + "], new: [" + pos + "]");
			}
		}
	}
	
	public void addGoalResult(Position pos, ZEvesOutput result) {
		checkPositionLegal(pos);
		addResult(new PositionInfo(pos, ResultType.GOAL), result);
	}
	
	public void addProofResult(Position pos, ProofScript script, Integer zEvesStepIndex,
			ZEvesOutput result) {
		
		checkPositionLegal(pos);
		
		String goalName = getScriptName(script);
		addResult(new ProofStepPosition(pos, goalName, zEvesStepIndex), result);
	}
	
	public int getLastPositionOffset() {
		return getEnd(getLastPosition());
	}
	
	private static int getEnd(Position pos) {
		
		if (pos == null) {
			return -1;
		}
		
		return pos.getOffset() + pos.getLength();
	}
	
	private Position getLastPosition() {
		if (positionResults.isEmpty()) {
			return null;
		}
		
		return positionResults.get(positionResults.size() - 1).getKey().getPosition();
	}
	
	private PositionInfo getLastPositionInfo(ResultType type) {
		
		for (int index = positionResults.size() - 1; index >= 0; index--) {
			Entry<PositionInfo, Object> result = positionResults.get(index);
			if (result.getKey().getType() == type) {
				return result.getKey();
			}
		}
		
		return null;
	}
	
	public Object getResult(Position pos) {
		
		Entry<PositionInfo, Object> result = getResultEntry(pos);
		if (result == null) {
			return null;
		}
		
		return result.getValue();
	}
	
	private Entry<PositionInfo, Object> getResultEntry(Position pos) {
		// wrap the position into entry to allow for searching
		Entry<PositionInfo, Object> posKey = 
				new SimpleEntry<PositionInfo, Object>(new PositionInfo(pos, null), null);
		
		// do binary search that stops if a position overlapping the given is found
		int found = Collections.binarySearch(positionResults, posKey, POSITION_OVERLAP);
		if (found < 0) {
			return null;
		}
		
		return positionResults.get(found);
	}
	
	public Object getProofResult(Position pos) {
		
		Entry<PositionInfo, Object> result = getResultEntry(pos);
		if (result == null) {
			return null;
		}
		
		PositionInfo posInfo = result.getKey();
		if (posInfo.getType() == ResultType.PROOF) {
			int stepIndex = ((ProofStepPosition) posInfo).getStepIndex();
			return new ProofResult(stepIndex, (ZEvesOutput) result.getValue());
		}
		
		return result.getValue();
	}
	
	public void clear() {
		positionResults.clear();
	}
	
	public void undoThrough(ZEvesApi zEvesApi, Position pos) throws ZEvesException {
		
		int undoThroughHistoryIndex = -1;
		Map<String, Integer> proofUndoCounts = new HashMap<String, Integer>();
		
		boolean removing = false;
		for (Iterator<Entry<PositionInfo, Object>> it = positionResults.iterator(); it.hasNext(); ) {
			
			PositionInfo resultPos = it.next().getKey();
			if (!removing && beforePos(resultPos, pos)) {
				// still before the position
				continue;
			}
			
			// removing - mark for 'back' and remove from list as well as results map
			removing = true;
			
			switch (resultPos.getType()) {
			case PARA: {
				/*
				 * For paragraphs, mark the first history index available in the
				 * "remove" zone - then undo through to (including) this
				 */
				if (undoThroughHistoryIndex < 0) {
					undoThroughHistoryIndex = ((ParaPosition) resultPos).getHistoryIndex();
				}
				break;
			}
			case PROOF: {
				/*
				 * For proofs, increment undo count for the given goal name -
				 * each proof steps means one "back" sent to Z/Eves for that
				 * particular goal
				 */
				ProofStepPosition proofPos = (ProofStepPosition) resultPos;
				String goalName = proofPos.getGoalName();
				
				// increment undo count
				Integer undoCount = proofUndoCounts.get(goalName);
				proofUndoCounts.put(goalName, (undoCount != null ? undoCount.intValue() : 0) + 1);
				break;
			}
			default: {
				/*
				 * For the rest (goals and errors), do nothing special, they
				 * will be just removed from the list, since we do not need to
				 * undo them in Z/Eves. Errors are not sent to Z/Eves at all,
				 * while goals are attached to the theorem paragraphs.
				 */
			}
			}
			
			// remove result from the list
			it.remove();
		}
		
		// undo proofs
		for (Entry<String, Integer> countEntry : proofUndoCounts.entrySet()) {
			String goalName = countEntry.getKey();
			int undoCount = countEntry.getValue();
			
			zEvesApi.setCurrentGoalName(goalName);
			zEvesApi.back(undoCount);
		}
		
		// undo paragraphs
		if (undoThroughHistoryIndex > 0) {
			zEvesApi.undoBackThrough(undoThroughHistoryIndex);
		}
	}
	
	private String getScriptName(ProofScript script) {
		return script.getZName().getWord(); 
	}
	
	private boolean beforePos(PositionInfo info, Position pos) {
		return beforePos(info.getPosition(), pos);
	}
	
	private static boolean beforePos(Position elemPos, Position pos) {
		int elemEnd = getEnd(elemPos);
		return elemEnd < pos.getOffset();
	}

	private class PositionInfo {
		
		private final Position pos;
		private final ResultType type;
		
		public PositionInfo(Position pos, ResultType type) {
			this.pos = pos;
			this.type = type;
		}
		
		public Position getPosition() {
			return pos;
		}

		public ResultType getType() {
			return type;
		}
	}
	
	private class ParaPosition extends PositionInfo {
		
		private final int historyIndex;
		
		public ParaPosition(Position pos, int historyIndex) {
			super(pos, ResultType.PARA);
			this.historyIndex = historyIndex;
		}
		
		public int getHistoryIndex() {
			return historyIndex;
		}
	}
	
	private class ProofStepPosition extends PositionInfo {
		
		private final String goalName;
		private final Integer zEvesStepIndex;
		
		public ProofStepPosition(Position pos, String goalName, Integer zEvesStepIndex) {
			super(pos, ResultType.PROOF);
			this.goalName = goalName;
			this.zEvesStepIndex = zEvesStepIndex;
		}
		
		public String getGoalName() {
			return goalName;
		}

		public Integer getStepIndex() {
			return zEvesStepIndex;
		}
	}
	
	private static class PositionOverlapComparator implements Comparator<Entry<PositionInfo, Object>> {

		@Override
		public int compare(Entry<PositionInfo, Object> o1, Entry<PositionInfo, Object> o2) {
			
			Position p1 = o1.getKey().getPosition();
			Position p2 = o2.getKey().getPosition();
			
			if (p1.overlapsWith(p2.getOffset(), p2.getLength())) {
				// consider them equal
				return 0;
			}
			
			if (p1.getOffset() <= p2.getOffset()) {
				return -1;
			} else {
				return 1;
			}
		}
		
	}
	
	public static class ProofResult {
		private final Integer stepIndex;
		private final ZEvesOutput result;
		
		public ProofResult(Integer stepIndex, ZEvesOutput result) {
			this.stepIndex = stepIndex;
			this.result = result;
		}

		public Integer getStepIndex() {
			return stepIndex;
		}

		public ZEvesOutput getResult() {
			return result;
		}
	}
	
}
