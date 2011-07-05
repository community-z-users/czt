package net.sourceforge.czt.eclipse.zeves.views;

import net.sourceforge.czt.zeves.ZEvesApi;
import net.sourceforge.czt.zeves.ZEvesException;

public interface IZEvesElement {

	public String getDescription();
	
	public Object loadContents(ZEvesApi api) throws ZEvesException;
	
}
