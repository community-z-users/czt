package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.z.ast.Para;

public abstract class AbstractVCGContext<T, B> implements VCGContext<T, B> {

	@Override
	public boolean isVCGContextPara(Para term) 
	{
		return false;
	}

}
