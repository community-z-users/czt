/**
 * Created on 2005-10-19
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.latex;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;

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
  
  private static final String BEGIN_TAG = "\\begin";

  public final static String[] Z_PARTITION_TYPES_LATEX = new String[]{
      IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR,
      IZPartitions.Z_PARAGRAPH_LATEX_ZED,
      IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION,
      IZPartitions.Z_PARAGRAPH_LATEX_AXDEF,
      IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA,
      IZPartitions.Z_PARAGRAPH_LATEX_GENAX,
      IZPartitions.Z_PARAGRAPH_LATEX_THEOREM,
      IZPartitions.Z_PARAGRAPH_LATEX_PROOFSCRIPT};

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
        IZPartitions.Z_PARAGRAPH_LATEX_THEOREM);
    IToken zParagraphLatexProofScript = new Token(
        IZPartitions.Z_PARAGRAPH_LATEX_PROOFSCRIPT);

    // Add rule for single line Z char conversion
    rules.add(new EndOfLineRule(IZPartitions.Z_PARAGRAPH_LATEX_ZCHAR_START,
        zParagraphLatexZChar)); 

    // Add rules for multi-line Z paragraphs.
    addDisableableRule(rules, IZPartitions.Z_PARAGRAPH_LATEX_ZED_START,
        IZPartitions.Z_PARAGRAPH_LATEX_ZED_END, zParagraphLatexZed); 
    addDisableableRule(rules, IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION_START,
        IZPartitions.Z_PARAGRAPH_LATEX_ZSECTION_END, zParagraphLatexZSection); 
    addDisableableRule(rules, IZPartitions.Z_PARAGRAPH_LATEX_AXDEF_START,
        IZPartitions.Z_PARAGRAPH_LATEX_AXDEF_END, zParagraphLatexAxdef); 
    addDisableableRule(rules, IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA_START,
        IZPartitions.Z_PARAGRAPH_LATEX_SCHEMA_END, zParagraphLatexSchema); 
    addDisableableRule(rules, IZPartitions.Z_PARAGRAPH_LATEX_GENAX_START,
        IZPartitions.Z_PARAGRAPH_LATEX_GENAX_END, zParagraphLatexGenAx); 
    addDisableableRule(rules, IZPartitions.Z_PARAGRAPH_LATEX_THEOREM_START,
        IZPartitions.Z_PARAGRAPH_LATEX_THEOREM_END, zParagraphLatexTheorem); 
    addDisableableRule(rules, IZPartitions.Z_PARAGRAPH_LATEX_PROOFSCRIPT_START,
        IZPartitions.Z_PARAGRAPH_LATEX_PROOFSCRIPT_END, zParagraphLatexProofScript);
    
    IPredicateRule[] result = new IPredicateRule[rules.size()];
    rules.toArray(result);

    setPredicateRules(result);
  }
  
  private void addRule(List<IPredicateRule> rules, String startSequence, String endSequence,
      IToken token)
  {
    rules.add(new MultiLineRule(startSequence, endSequence, token, (char) 0, true));
  }
  
  private void addDisableableRule(List<IPredicateRule> rules, String startSequence, String endSequence,
      IToken token)
  {
    addRule(rules, startSequence, endSequence, token);
    if (startSequence.startsWith(BEGIN_TAG)) {
      String disabledSeq = BEGIN_TAG + "[disabled]" + startSequence.substring(BEGIN_TAG.length());
      addRule(rules, disabledSeq, endSequence, token);
    }
  }
}
