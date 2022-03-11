/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import net.sourceforge.czt.z.util.ZString;


/**
 * @author Chengdong Xu
 *
 */
public class ZCharacter
{
  /**
   * The Constructor
   */
  public ZCharacter()
  {
    super();
  }

  public static boolean isZWordStart(char character)
  {
    return isZLaTexWordStart(character) || isZUnicodeWordStart(character);
  }

  public static boolean isZLaTexWordStart(char character)
  {
    return Character.isLetter(character) || (character == '\\');
  }

  public static boolean isZUnicodeWordStart(char character)
  {
    return Character.isLetter(character);
  }

  public static boolean isZWordPart(char character)
  {
    return isZLaTexWordPart(character) || isZUnicodeWordPart(character);
  }

  public static boolean isZLaTexWordPart(char character)
  {
    return Character.isLetterOrDigit(character) || (character == '_')
        || (character == '?') || (character == '!' || (character == '\''));
  }

  public static boolean isZUnicodeWordPart(char character)
  {
    return Character.isLetterOrDigit(character) || (character == '?')
        || (character == '!') || (character == PRIME);
  }

  public static boolean isZLaTexWhitespace(char character)
  {
    return Character.isWhitespace(character);
  }

  public static boolean isZUnicodeWhitespace(char character)
  {
    return Character.isWhitespace(character);
  }

  /**
   * left parenthesis.
   */
  public static final char LPAREN = ZString.LPAREN.charAt(0);

  /**
   * right parenthesis.
   */
  public static final char RPAREN = ZString.RPAREN.charAt(0);

  /**
   * left square bracket.
   */
  public static final char LSQUARE = ZString.LSQUARE.charAt(0);

  /**
   * right square bracket.
   */
  public static final char RSQUARE = ZString.RSQUARE.charAt(0);

  /**
   * left curly bracket.
   */
  public static final char LBRACE = ZString.LBRACE.charAt(0);

  /**
   * right curly bracket.
   */
  public static final char RBRACE = ZString.RBRACE.charAt(0);

  /**
   * Z notation left binding bracket.
   */
  public static final char LBIND = ZString.LBIND.charAt(0);

  /**
   * Z notation right binding bracket.
   */
  public static final char RBIND = ZString.RBIND.charAt(0);

  /**
   * mathmatical left double angle bracket.
   */
  public static final char LDATA = ZString.LDATA.charAt(0);

  /**
   * mathmatical right double angle bracket.
   */
  public static final char RDATA = ZString.RDATA.charAt(0);

  /**
   * Z notation left image bracket.
   */
  public static final char LIMG = ZString.LIMG.charAt(0);

  /**
   * Z notation right image bracket.
   */
  public static final char RIMG = ZString.RIMG.charAt(0);

  /**
   * mathmatical left angle bracket.
   */
  public static final char LANGLE = ZString.LANGLE.charAt(0);

  /**
   * mathmatical right angle bracket.
   */
  public static final char RANGLE = ZString.RANGLE.charAt(0);

  public static final String[] BRACKETS_LATEX = {"(", ")", "[", "]", "{", "}",
      "\\{", "\\}", "\\lblot", "\\rblot", "\\langle", "\\rangle", "\\ldata",
      "\\rdata", "\\limg", "\\rimg"};

  public static final char[] BRACKETS_UNICODE = {LPAREN, RPAREN, LSQUARE,
      RSQUARE, LBRACE, RBRACE, LBIND, RBIND, LDATA, RDATA, LIMG, RIMG, LANGLE,
      RANGLE};
  
  /**
   * Prime decoration
   */
  public static final char PRIME = ZString.PRIME.charAt(0);
}
