/**
 * 
 */

package net.sourceforge.czt.eclipse.editors.latex;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.eclipse.editors.AbstractZCodeScanner;
import net.sourceforge.czt.eclipse.util.IColorManager;
import net.sourceforge.czt.eclipse.util.IZColorConstants;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;

/**
 * @author Chengdong Xu
 *
 */
public class ZCharCodeScanner extends AbstractZCodeScanner
{

  private static String[] fgZCharKeywords = {};

  private static String[] fgTokenProperties = {IZColorConstants.CZT_COMMENT,};

  /**
   * Create a ZCHAR code scanner
   * @param manager
   * @param store
   */
  public ZCharCodeScanner(IColorManager manager, IPreferenceStore store)
  {
    super(manager, store);
    initialize();
  }

  /*
   * @see net.sourceforge.czt.eclipse.editors.AbstractZCodeScanner#getTokenProperties()
   */
  @Override
  protected String[] getTokenProperties()
  {
    return fgTokenProperties;
  }

  /*
   * @see net.sourceforge.czt.eclipse.editors.AbstractZCodeScanner#createRules()
   */
  @Override
  /**
   * @see net.sourceforge.czt.eclipse.editors.AbstractZCodeScanner#createRules()
   */
  protected List<IRule> createRules()
  {
    List<IRule> rules = new ArrayList<IRule>();

    //        IToken keywordToken = getToken(IZColorConstants.CZT_KEYWORD);
    //        IToken defaultToken = getToken(IZColorConstants.CZT_DEFAULT);
    IToken singleLineCommentToken = getToken(IZColorConstants.CZT_COMMENT);

    // Add generic whitespace rule.
    //        rules.add(new WhitespaceRule(new ZLatexWhitespaceDetector()));

    // Add word rule for keywords, types, tags and constants.
    //        WordRule wordRule = new WordRule(new ZLatexWordDetector(), defaultToken);

    //        for (int i = 0; i < fgZCharKeywords.length; i++)
    //            wordRule.addWord(fgZCharKeywords[i], keywordToken);

    ///        rules.add(wordRule);
    
    setDefaultReturnToken(singleLineCommentToken);

    return rules;
  }

}
