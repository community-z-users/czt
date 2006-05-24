/**
 * Created on 2005-10-19
 */
package net.sourceforge.czt.eclipse.editors.latex;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

/**
 * @author Chengdong Xu
 */
public class ZLatexPartitionScanner extends RuleBasedPartitionScanner {

	public final static String Z_PARAGRAPH_LATEX_ZCHAR = "__z_paragraph_latex_zchar"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_ZSECTION = "__z_paragraph_latex_zsection"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_ZED = "__z_paragraph_latex_zed"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_SCHEMA = "__z_paragraph_latex_schema"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_AXDEF = "__z_paragraph_latex_axdef"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_GENDEF = "__z_paragraph_latex_gendef"; //$NON-NLS-1$

	public final static String[] Z_PARTITION_TYPES_LATEX = new String[] { Z_PARAGRAPH_LATEX_ZCHAR, Z_PARAGRAPH_LATEX_ZSECTION, Z_PARAGRAPH_LATEX_ZED, Z_PARAGRAPH_LATEX_SCHEMA, Z_PARAGRAPH_LATEX_AXDEF, Z_PARAGRAPH_LATEX_GENDEF };

	/**
	 * Creates the partitioner and sets up the appropriate rules.
	 */
	public ZLatexPartitionScanner() {
		super();
		List<IPredicateRule> rules= new ArrayList<IPredicateRule>();
		
		IToken zParagraphLatexZChar = new Token(Z_PARAGRAPH_LATEX_ZCHAR);
		IToken zParagraphLatexZSection = new Token(Z_PARAGRAPH_LATEX_ZSECTION);
		IToken zParagraphLatexZed = new Token(Z_PARAGRAPH_LATEX_ZED);
		IToken zParagraphLatexSchema = new Token(Z_PARAGRAPH_LATEX_SCHEMA);
		IToken zParagraphLatexAxdef = new Token(Z_PARAGRAPH_LATEX_AXDEF);
		IToken zParagraphLatexGendef = new Token(Z_PARAGRAPH_LATEX_GENDEF);
			
		// Add rule for single line Z char conversion
		rules.add(new EndOfLineRule("%%zchar", zParagraphLatexZChar)); //$NON-NLS-1$
			
		// Add rules for multi-line Z specifiction.
		rules.add(new MultiLineRule("\\begin{zsection}", "\\end{zsection}", zParagraphLatexZSection, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		rules.add(new MultiLineRule("\\begin{zed}", "\\end{zed}", zParagraphLatexZed, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		rules.add(new MultiLineRule("\\begin{schema}", "\\end{schema}", zParagraphLatexSchema, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		rules.add(new MultiLineRule("\\begin{axdef}", "\\end{acdef}", zParagraphLatexAxdef, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		rules.add(new MultiLineRule("\\begin{gendef}", "\\end{gendef}", zParagraphLatexGendef, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		
		IPredicateRule[] result= new IPredicateRule[rules.size()];
		rules.toArray(result);
		
		setPredicateRules(result);
	}
}
