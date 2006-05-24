package net.sourceforge.czt.eclipse.editors.unicode;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

public class ZUnicodePartitionScanner extends RuleBasedPartitionScanner {
	public final static String Z_PARAGRAPH_UNICODE = "__z_paragraph_unicode"; //$NON-NLS-1$
	
	public final static String[] Z_PARTITION_TYPES_UNICODE = new String[] { Z_PARAGRAPH_UNICODE };
	
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
	public ZUnicodePartitionScanner() {
		super();
		List<IPredicateRule> rules= new ArrayList<IPredicateRule>();
		IToken zParagraphUnicode = new Token(Z_PARAGRAPH_UNICODE);
		// Add special case word rule.
//		rules.add(new WordPredicateRule(zMultiLineComment));
		
		//Add rules for multi-line Z specifiction.
		rules.add(new MultiLineRule("\u2500", "\u2029", zParagraphUnicode, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
		
		IPredicateRule[] result= new IPredicateRule[rules.size()];
		rules.toArray(result);
		
		setPredicateRules(result);
	}
}
