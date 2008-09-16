/**
 * Created on 2005-10-19
 */

package net.sourceforge.czt.eclipse.editors.latex;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.editors.IZPartitions;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;

/**
 * @author Chengdong Xu
 */
public class ZLatexPartitionScanner extends RuleBasedPartitionScanner
{

  public final static String[] Z_PARTITION_TYPES_LATEX = new String[]{
      IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR,
      IZPartitions.Z_PARAGRAPH_LATEX_ZED,
      IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION,
      IZPartitions.Z_PARAGRAPH_LATEX_AXDEF,
      IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA,
      IZPartitions.Z_PARAGRAPH_LATEX_GENAX,
      IZPartitions.Z_PARAGRAPH_LATEX_THEOREM};

  /**
   * Creates the partitioner and sets up the appropriate rules.
   */
  public ZLatexPartitionScanner()
  {
    super();
    List<IPredicateRule> rules = new ArrayList<IPredicateRule>();

    IToken zParagraphLatexZChar = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR);
    IToken zParagraphLatexZed = new Token(IZPartitions.Z_PARAGRAPH_LATEX_ZED);
    IToken zParagraphLatexZSection = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION);
    IToken zParagraphLatexAxdef = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_AXDEF);
    IToken zParagraphLatexSchema = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA);
    IToken zParagraphLatexGenAx = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_GENAX);
    IToken zParagraphLatexTheorem = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_GENAX);

    // Add rule for single line Z char conversion
    rules.add(new EndOfLineRule(IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR_START,
        zParagraphLatexZChar)); //$NON-NLS-1$

    // Add rules for multi-line Z paragraphs.
    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_LATEX_ZED_START,
        IZPartitions.Z_PARAGRAPH_LATEX_ZED_END, zParagraphLatexZed, (char) 0,
        true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION_START,
        IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION_END, zParagraphLatexZSection,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_LATEX_AXDEF_START,
        IZPartitions.Z_PARAGRAPH_LATEX_AXDEF_END, zParagraphLatexAxdef,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA_START,
        IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA_END, zParagraphLatexSchema,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_LATEX_GENAX_START,
        IZPartitions.Z_PARAGRAPH_LATEX_GENAX_END, zParagraphLatexGenAx,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(IZPartitions.Z_PARAGRAPH_LATEX_THEOREM_START,
        IZPartitions.Z_PARAGRAPH_LATEX_THEOREM_END, zParagraphLatexTheorem,
        (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    
    IPredicateRule[] result = new IPredicateRule[rules.size()];
    rules.toArray(result);

    setPredicateRules(result);
  }
}
