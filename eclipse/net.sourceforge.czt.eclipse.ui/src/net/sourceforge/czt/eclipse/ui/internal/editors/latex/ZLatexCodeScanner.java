
package net.sourceforge.czt.eclipse.ui.internal.editors.latex;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.ui.internal.editors.AbstractZCodeScanner;
import net.sourceforge.czt.eclipse.ui.internal.util.IColorManager;
import net.sourceforge.czt.eclipse.ui.internal.util.IZColorConstants;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.WhitespaceRule;
import org.eclipse.jface.text.rules.WordRule;

/**
 * @author Chengdong Xu
 *
 * This class defines the syntax colouring for LaTeX markup.
 */
public class ZLatexCodeScanner extends AbstractZCodeScanner
{

  /** Taken from Section 7.4.2 of the Z standard.
   *  Plus "theorem", which is a CZT extension for named conjectures.
   */
	// TODO: this is horrible. Should reflect ZKeyword.values this whole set of classes needs refactoring...? Leo
  private static String[] fgAlphabeticKeywords = //ZKeyword.values();
	  {"\\begin", "\\end", "else",
      "false", "function", "generic", "if", "leftassoc", "let", "\\power",
      "parents", "pre", "relation", "rightassoc", "section", "then",
      "true", "theorem"};

  private static String[] fgSymbolicKeywords = {":", "==", ",", "::=", "|",
      "&", "\\", "/", ".", ";", "-", ",,", "=", ""};

  /**
   * A.2.4 Core characters and words in Latex markup
   */
  // Greak alphabet characters
  private static String[] fgGreakCharacters = {"\\Delta", "\\Xi", "\\theta",
      "\\lambda", "\\mu"};

  // Other letter characters
  private static String[] fgOtherLetterCharacters = {"\\arithmos", "\\nat",
      "\\power"};

  // Special characters
  private static String[] fgSpecialCharacters = {"\\_", "\\{", "\\\\ldata}",
      "\\rdata", "\\lblot", "\\rblot"};

  // Symbol characters
  private static String[] fgSymbolCharacters = {"\\vdash", "\\land", "\\lor",
      "\\implies", "\\iff", "\\lnot", "\\forall", "\\exists", "\\cross",
      "\\in", "\\hide", "\\project", "\\semi", "\\pipe"};

  private static String[] fgTokenProperties = { IZColorConstants.CZT_KEYWORD,
      IZColorConstants.CZT_OPERATOR, IZColorConstants.CZT_DEFAULT,
      IZColorConstants.CZT_COMMENT };

  /**
   * Creates a Z latex code scanner
   *
   * @param colorManager   the color manager
   * @param store     the preference store
   */
  public ZLatexCodeScanner(IColorManager colorManager, IPreferenceStore store)
  {
    super(colorManager, store);
    initialize();
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.internal.editors.AbstractZCodeScanner#getTokenProperties()
   */
  protected String[] getTokenProperties()
  {
    return fgTokenProperties;
  }

  /**
   * @see net.sourceforge.czt.eclipse.ui.internal.editors.AbstractZCodeScanner#createRules()
   */
  protected List<IRule> createRules()
  {
    List<IRule> rules = new ArrayList<IRule>();

    IToken keywordToken = getToken(IZColorConstants.CZT_KEYWORD);
    IToken singleLineCommentToken = getToken(IZColorConstants.CZT_COMMENT);
    IToken defaultToken = getToken(IZColorConstants.CZT_DEFAULT);

    // Add rule for single line comments.
    rules.add(new EndOfLineRule("%", singleLineCommentToken, '%')); //$NON-NLS-1$
    // Add rule for strings and character constants.
    // rules.add(new SingleLineRule("\"", "\"", stringToken, '\\'));
    // //$NON-NLS-2$ //$NON-NLS-1$
    // rules.add(new SingleLineRule("'", "'", stringToken, '\\'));
    // //$NON-NLS-2$ //$NON-NLS-1$

    // Add generic whitespace rule.
    rules.add(new WhitespaceRule(new ZLatexWhitespaceDetector()));

    // Add word rule for keywords, types, tags and constants.
    WordRule wordRule = new WordRule(new ZLatexWordDetector(), defaultToken);

    for (int i = 0; i < fgAlphabeticKeywords.length; i++)
      wordRule.addWord(fgAlphabeticKeywords[i], keywordToken);
    for (int i = 0; i < fgSymbolicKeywords.length; i++)
      wordRule.addWord(fgSymbolicKeywords[i], keywordToken);
    for (int i = 0; i < fgGreakCharacters.length; i++)
      wordRule.addWord(fgGreakCharacters[i], keywordToken);
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