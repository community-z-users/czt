/**
 * Created on 2005-10-19
 */
package net.sourceforge.czt.eclipse.editors;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.util.IZFileType;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

/**
 * @author Chengdong Xu
 */
public class ZPartitionScanner extends RuleBasedPartitionScanner {

	public final static String Z_PARAGRAPH_LATEX_ZCHAR = "__z_paragraph_latex_zchar"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_ZSECTION = "__z_paragraph_latex_zsection"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_ZED = "__z_paragraph_latex_zed"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_SCHEMA = "__z_paragraph_latex_schema"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_AXDEF = "__z_paragraph_latex_axdef"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_LATEX_GENDEF = "__z_paragraph_latex_gendef"; //$NON-NLS-1$

	public final static String Z_PARAGRAPH_UTF8 = "__z_paragraph_utf8"; //$NON-NLS-1$
	public final static String Z_PARAGRAPH_UTF16 = "__z_paragraph_utf16"; //$NON-NLS-1$
	
	public final static String[] Z_PARTITION_TYPES_LATEX = new String[] { Z_PARAGRAPH_LATEX_ZCHAR, Z_PARAGRAPH_LATEX_ZSECTION, Z_PARAGRAPH_LATEX_ZED, Z_PARAGRAPH_LATEX_SCHEMA, Z_PARAGRAPH_LATEX_AXDEF, Z_PARAGRAPH_LATEX_GENDEF };
	public final static String[] Z_PARTITION_TYPES_UTF8 = new String[] { Z_PARAGRAPH_UTF8 };
	public final static String[] Z_PARTITION_TYPES_UTF16 = new String[] { Z_PARAGRAPH_UTF16 };

	/**
	 * Detector for empty comments.
	 */
//	static class EmptyCommentDetector implements IWordDetector {
//
//		/* (non-Javadoc)
//		* Method declared on IWordDetector
//	 	*/
//		public boolean isWordStart(char character) {
//			return (character == '/');
//		}
//
//		/* (non-Javadoc)
//		* Method declared on IWordDetector
//	 	*/
//		public boolean isWordPart(char character) {
//			return (character == '*' || character == '/');
//		}
//	}
	
	/**
	 * 
	 */
//	static class WordPredicateRule extends WordRule implements IPredicateRule {
//		
//		private IToken fSuccessToken;
//		
//		public WordPredicateRule(IToken successToken) {
//			super(new EmptyCommentDetector());
//			fSuccessToken= successToken;
//			addWord("/**/", fSuccessToken); //$NON-NLS-1$
//		}
//		
//		/*
//		 * @see org.eclipse.jface.text.rules.IPredicateRule#evaluate(ICharacterScanner, boolean)
//		 */
//		public IToken evaluate(ICharacterScanner scanner, boolean resume) {
//			return super.evaluate(scanner);
//		}
//
//		/*
//		 * @see org.eclipse.jface.text.rules.IPredicateRule#getSuccessToken()
//		 */
//		public IToken getSuccessToken() {
//			return fSuccessToken;
//		}
//	}

	/**
	 * Creates the partitioner and sets up the appropriate rules.
	 */
	public ZPartitionScanner(String fileType) {
		super();
		List rules= new ArrayList();
		
		if ((fileType == null) || fileType.equals("")) {
			
		}
		else if (fileType.equals(IZFileType.FILETYPE_LATEX)) {
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
		}
		else if (fileType.equals(IZFileType.FILETYPE_UTF8)) {
			IToken zParagraphUtf8 = new Token(Z_PARAGRAPH_UTF8);
			//Add rules for multi-line Z specifiction.
			rules.add(new MultiLineRule("\u2500", "\u2029", zParagraphUtf8, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		}
		else if (fileType.equals(IZFileType.FILETYPE_UTF16)) {
			IToken zParagraphUtf16 = new Token(Z_PARAGRAPH_UTF16);
			// Add special case word rule.
//			rules.add(new WordPredicateRule(zMultiLineComment));
			
			//Add rules for multi-line Z specifiction.
			rules.add(new MultiLineRule("\u2500", "\u2029", zParagraphUtf16, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		}
		else {
			
		}
		
		IPredicateRule[] result= new IPredicateRule[rules.size()];
		rules.toArray(result);
		
		setPredicateRules(result);
	}
}
