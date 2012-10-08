
package net.sourceforge.czt.eclipse.ui.editors.unicode;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.editors.AbstractZCodeScanner;
import net.sourceforge.czt.eclipse.ui.util.IColorManager;
import net.sourceforge.czt.eclipse.ui.util.IZColorConstants;
import net.sourceforge.czt.z.util.ZString;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

/**
 * @author Chengdong Xu
 *
 * This class defines the syntax colouring for Unicode markup.
 */
public class ZUnicodeCodeScanner extends AbstractZCodeScanner
{
  /** Taken from Section 7.4.2 of the Z standard.
   *  Plus "theorem", which is a CZT extension for named conjectures.
   */
  private static String[] fgAlphabeticKeywords = {"else", "false", "function",
      "generic", "if", "leftassoc", "let", "parents", "pre", "relation",
      "rightassoc", "section", "then", "true", "theorem"};

  private static String[] fgSymbolicKeywords = {":", "==", ",", "::=", "|",
      "&", "\\", "/", ".", ";", "-", ",,", "=", ""};

  /**
   * A.2.4 Core characters and words in Latex markup
   */
  // Greek alphabet characters
  private static String[] fgGreekCharacters = {"\\Delta", "\\Xi", "\\theta",
      ZString.LAMBDA, "\\mu"};

  // Other letter characters
  private static String[] fgOtherLetterCharacters = {"\\arithmos", "\\nat",
      "\\power"};

  // Special characters
  private static String[] fgSpecialCharacters = {"\\_", "\\{", "\\\\ldata}",
      "\\rdata", "\\lblot", "\\rblot"};

  // Symbol characters
  private static String[] fgSymbolCharacters = {"\\vdash", "\\land", "\\lor",
      ZString.IMP, "\\implies", "\\iff", "\\lnot", "\\forall", "\\exists", "\\cross",
      "\\in", "\\hide", "\\project", "\\semi", "\\pipe"};

  private static String[] fgTokenProperties = {
      IZColorConstants.CZT_KEYWORD, IZColorConstants.CZT_OPERATOR,
      IZColorConstants.CZT_DEFAULT, IZColorConstants.CZT_COMMENT, };

  /**
   * Creates a Z unicode code scanner
   * @param colorManager the color manager
   * @param store the preference store
   */
  public ZUnicodeCodeScanner(IColorManager colorManager, IPreferenceStore store)
  {
    super(colorManager, store);
    initialize();
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.editors.AbstractZCodeScanner#getTokenProperties()
   */
  protected String[] getTokenProperties()
  {
    return fgTokenProperties;
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.editors.AbstractZCodeScanner#createRules()
   */

  protected List<IRule> createRules()
  {
    List<IRule> rules = new ArrayList<IRule>();

    IToken keywordToken = getToken(IZColorConstants.CZT_KEYWORD);
    IToken singleLineCommentToken = getToken(IZColorConstants.CZT_COMMENT);
    IToken defaultToken = getToken(IZColorConstants.CZT_DEFAULT);

    // Add rule for single line comments.
    rules.add(new EndOfLineRule("%", singleLineCommentToken, '%')); //$NON-NLS-1$

    // Add generic whitespace rule.
    rules.add(new WhitespaceRule(new ZUnicodeWhitespaceDetector()));

    // Add word rule for keywords, types, tags and constants.
    WordRule wordRule = new WordRule(new ZUnicodeWordDetector(), defaultToken);

    for (int i = 0; i < fgAlphabeticKeywords.length; i++)
      wordRule.addWord(fgAlphabeticKeywords[i], keywordToken);
    for (int i = 0; i < fgSymbolicKeywords.length; i++)
      wordRule.addWord(fgSymbolicKeywords[i], keywordToken);
    for (int i = 0; i < fgGreekCharacters.length; i++)
      wordRule.addWord(fgGreekCharacters[i], keywordToken);
    for (int i = 0; i < fgOtherLetterCharacters.length; i++)
      wordRule.addWord(fgOtherLetterCharacters[i], keywordToken);
    for (int i = 0; i < fgSpecialCharacters.length; i++)
      wordRule.addWord(fgSpecialCharacters[i], keywordToken);
    for (int i = 0; i < fgSymbolCharacters.length; i++)
      wordRule.addWord(fgSymbolCharacters[i], keywordToken);

    rules.add(wordRule);
    
    setDefaultReturnToken(defaultToken);

    return rules;
  }
}
