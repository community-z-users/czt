package net.sourceforge.czt.zeves.snapshot;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.zeves.response.ZEvesOutput;

public class SnapshotData {

	private final Term term;
	
	private final Object result;
	private final List<ZEvesOutput> trace;
	
	private final String goalName;
	private final int zEvesProofStepIndex;
	
	public static class Builder {
		
		private final Term term;
		private Object result;
		
		private List<ZEvesOutput> trace = new ArrayList<ZEvesOutput>();
		
		private String goalName;
		private int zEvesProofStepIndex = -1;
		
		public Builder(Term term) {
			this.term = term;
		}
		
		public Builder result(Object result) {
			this.result = result;
			return this;
		}
		
		public Builder trace(List<? extends ZEvesOutput> trace) {
			this.trace = new ArrayList<ZEvesOutput>(trace);
			return this;
		}
		
		public Builder goalName(String goalName) {
			this.goalName = goalName;
			return this;
		}
		
		public Builder proofStep(int zEvesProofStepIndex) {
			this.zEvesProofStepIndex = zEvesProofStepIndex;
			return this;
		}
		
		public Builder goal() {
			return proofStep(ZEvesSnapshot.GOAL_STEP_INDEX);
		}
		
		public SnapshotData build() {
			return new SnapshotData(this);
		}
	}
	
	private SnapshotData(Builder builder) {
		this.term = builder.term;
		this.result = builder.result;
		this.trace = builder.trace;
		this.goalName = builder.goalName;
		this.zEvesProofStepIndex = builder.zEvesProofStepIndex;
	}

	public Term getTerm() {
		return term;
	}

	public Object getResult() {
		return result;
	}

	public List<ZEvesOutput> getTrace() {
		return Collections.unmodifiableList(trace);
	}

	public String getGoalName() {
		return goalName;
	}

	public int getProofStepIndex() {
		return zEvesProofStepIndex;
	}
	
}
