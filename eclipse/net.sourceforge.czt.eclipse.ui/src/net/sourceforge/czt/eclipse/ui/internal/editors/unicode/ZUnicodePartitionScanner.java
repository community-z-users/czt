
package net.sourceforge.czt.eclipse.ui.internal.editors.unicode;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;

import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

public class ZUnicodePartitionScanner extends RuleBasedPartitionScanner
{

  public final static String[] Z_PARTITION_TYPES_UNICODE = new String[]{
      IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION,
      IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF,
      IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA,
      IZPartitions.Z_PARAGRAPH_UNICODE_GENAX,
      IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH,
      IZPartitions.Z_PARAGRAPH_UNICODE_PROOFSCRIPT};

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
  public ZUnicodePartitionScanner()
  {
    super();
    List<IPredicateRule> rules = new ArrayList<IPredicateRule>();

    IToken zParagraphUnicodeZSection = new Token(
        IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION);
    IToken zParagraphUnicodeAxdef = new Token(
        IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF);
    IToken zParagraphUnicodeSchema = new Token(
        IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA);
    IToken zParagraphUnicodeGenAx = new Token(
        IZPartitions.Z_PARAGRAPH_UNICODE_GENAX);
    IToken zParagraphUnicodeGenSch = new Token(
        IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH);
    IToken zParagraphUnicodeProofScript = new Token(
        IZPartitions.Z_PARAGRAPH_UNICODE_PROOFSCRIPT);

    // Add special case word rule.
    // rules.add(new WordPredicateRule(zMultiLineComment));

    //Add rules for multi-line Z paragraphs. Remain the old EndChar(\u2029) for backward-compatibility
    rules.add(new MultiLineRule(
        IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION_START,
        IZPartitions.Z_PARAGRAPH_UNICODE_ZSECTION_END,
        zParagraphUnicodeZSection, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$

    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF_START,
        IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF_END, zParagraphUnicodeAxdef,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$

    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_UNICODE_SCHEMA_START,
        IZPartitions.Z_PARAGRAPH_UNICODE_AXDEF_END, zParagraphUnicodeSchema,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$

    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_UNICODE_GENAX_START,
        IZPartitions.Z_PARAGRAPH_UNICODE_GENAX_END, zParagraphUnicodeGenAx,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$

    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH_START,
        IZPartitions.Z_PARAGRAPH_UNICODE_GENSCH_END, zParagraphUnicodeGenSch,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    
    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_UNICODE_PROOFSCRIPT_START,
        IZPartitions.Z_PARAGRAPH_UNICODE_PROOFSCRIPT_END, zParagraphUnicodeProofScript,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$

    IPredicateRule[] result = new IPredicateRule[rules.size()];
    rules.toArray(result);

    setPredicateRules(result);
  }
}
