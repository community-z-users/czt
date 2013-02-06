package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.z.ast.ZName;

public interface VCGContext<T, B> 
{
	ZName getStateName();
	ZName getInitName();
	
	/**
	 * Get the operator 
	 * @param operationName
	 * @return
	 */
	T getOpType(ZName operationName);
	B getOpBindings(ZName operationName);
}
