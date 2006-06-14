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
      IZPartitions.Z_PARAGRAPH_LATEX_GENAX};

  /**
   * Creates the partitioner and sets up the appropriate rules.
   */
  public ZLatexPartitionScanner()
  {
    super();
    List<IPredicateRule> rules = new ArrayList<IPredicateRule>();

    IToken zParagraphLatexZChar = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR);
    IToken zParagraphLatexZed = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_ZED);
    IToken zParagraphLatexZSection = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION);
    IToken zParagraphLatexAxdef = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_AXDEF);
    IToken zParagraphLatexSchema = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA);
    IToken zParagraphLatexGenAx = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_GENAX);

    // Add rule for single line Z char conversion
    rules.add(new EndOfLineRule("%%zchar", zParagraphLatexZChar)); //$NON-NLS-1$

    // Add rules for multi-line Z paragraphs.
    rules.add(new MultiLineRule(
        "\\begin{zed}", "\\end{zed}", zParagraphLatexZed, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(
        "\\begin{zsection}", "\\end{zsection}", zParagraphLatexZSection, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(
        "\\begin{axdef}", "\\end{axdef}", zParagraphLatexAxdef, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(
        "\\begin{schema}", "\\end{schema}", zParagraphLatexSchema, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$
    rules.add(new MultiLineRule(
        "\\begin{gendef}", "\\end{gendef}", zParagraphLatexGenAx, (char) 0, true)); //$NON-NLS-1$ //$NON-NLS-2$

    IPredicateRule[] result = new IPredicateRule[rules.size()];
    rules.toArray(result);

    setPredicateRules(result);
  }
}
