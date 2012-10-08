package net.sourceforge.czt.eclipse.ui.views;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import net.sourceforge.czt.session.Markup;

public interface IZInfoObject {

	public Markup getMarkup();
	
	public String loadContents(Markup markup, IProgressMonitor monitor) throws CoreException;
	
	public String loadDescription(IProgressMonitor monitor) throws CoreException;
	
}
