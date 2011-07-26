package net.sourceforge.czt.eclipse.zeves;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.response.ZEvesOutput;

public class ZEvesFileState {

	private final Map<Para, Integer> historyIndices = new HashMap<Para, Integer>();
	private final Map<Para, Object> paraResults = new HashMap<Para, Object>();
	
	private final Map<ProofStepId, ZEvesOutput> proofStepResults = new HashMap<ProofStepId, ZEvesOutput>();

	public Integer getHistoryIndex(Para para) {
		return historyIndices.get(para);
	}
	
	public void addPara(Para para, int historyIndex) {
		historyIndices.put(para, historyIndex);
	}
	
	public void addParaResult(Para para, Object result) {
		paraResults.put(para, result);
	}
	
	public Object getParaResult(Para para) {
		return paraResults.get(para);
	}
	
	public void addProofResult(ProofScript script, int proofStep, ZEvesOutput result) {
		proofStepResults.put(new ProofStepId(script, proofStep), result);
	}
	
	public ZEvesOutput getProofResult(ProofScript script, int proofStep) {
		return proofStepResults.get(new ProofStepId(script, proofStep));
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
	
}
