package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.Collection;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;

import org.eclipse.jface.text.IDocument;

/**
 * @author Chengdong Xu
 */
public interface IOccurrencesFinder {
	
	public String initialize(Term root, int offset, int length);
	
	public List<?> perform();
	
	public String getJobLabel();

	public String getPluralLabel(String documentName);
	
	public String getSingularLabel(String documentName);
	
	public void collectOccurrenceMatches(Term term, IDocument document, Collection<?> resultingMatches);
}
