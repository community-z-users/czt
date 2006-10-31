/**
 * 
 */

package net.sourceforge.czt.eclipse.editors;


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
        || (character == '?') || (character == '!');
  }

  public static boolean isZUnicodeWordPart(char character)
  {
    return Character.isLetterOrDigit(character) || (character == '?')
        || (character == '!') || (character == '\'');
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
  public static final char LPAREN = '\u0028';

  /**
   * right parenthesis.
   */
  public static final char RPAREN = '\u0029';

  /**
   * left square bracket.
   */
  public static final char LSQUARE = '\u005B';

  /**
   * right square bracket.
   */
  public static final char RSQUARE = '\u005D';

  /**
   * left curly bracket.
   */
  public static final char LBRACE = '\u007B';

  /**
   * right curly bracket.
   */
  public static final char RBRACE = '\u007D';

  /**
   * Z notation left binding bracket.
   */
  public static final char LBIND = '\u2989';

  /**
   * Z notation right binding bracket.
   */
  public static final char RBIND = '\u298A';

  /**
   * mathmatical left double angle bracket.
   */
  //  public static final char LDATA = '\u300A';
  public static final char LDATA = '\u27EA';

  /**
   * mathmatical right double angle bracket.
   */
  //  public static final char RDATA = '\u300B'
  public static final char RDATA = '\u27EB';

  /**
   * Z notation left image bracket.
   */
  public static char LIMG = '\u2987';

  /**
   * Z notation right image bracket.
   */
  public static char RIMG = '\u2988';

  /**
   * mathmatical left angle bracket.
   */
  //  public static char LANGLE = '\u3008';
  public static char LANGLE = '\u27E8';

  /**
   * mathmatical right angle bracket.
   */
  //  public static char LANGLE = '\u3009';
  public static char RANGLE = '\u27E9';

  public final static String[] BRACKETS_LATEX = {"(", ")", "[", "]", "{", "}",
      "\\{", "\\}", "\\lblot", "\\rblot", "\\langle", "\\rangle", "\\ldata",
      "\\rdata", "\\limg", "\\rimg"};

  public final static char[] BRACKETS_UNICODE = {LPAREN, RPAREN, LSQUARE,
      RSQUARE, LBRACE, RBRACE, LBIND, RBIND, LDATA, RDATA, LIMG, RIMG, LANGLE,
      RANGLE};
}
