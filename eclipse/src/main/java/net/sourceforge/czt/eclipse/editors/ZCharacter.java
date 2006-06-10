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
  
  public final static char[] BRACKETS_LATEX = { '(', ')', '[', ']', '{', '}' };
  public final static char[] BRACKETS_UNICODE = { '\u0028', '\u0029', '\u005B', '\u005D', '\u007B', '\u007D', '\u2989', '\u298A', '\u300A', '\u300B', '\u2987', '\u2988', '\u27E8', '\u27E9' }; 

  /**
   * 
   */
  public ZCharacter()
  {
    super();
    // TODO Auto-generated constructor stub
  }

  public static boolean isZWordStart(char character)
  {
    return isZLatexWordStart(character) || isZUnicodeWordStart(character);
  }

  public static boolean isZLatexWordStart(char character)
  {
    return Character.isLetter(character) || (character == '\\');
  }

  public static boolean isZUnicodeWordStart(char character)
  {
    return Character.isLetter(character);
  }

  public static boolean isZWordPart(char character)
  {
    return isZLatexWordPart(character) || isZUnicodeWordPart(character);
  }

  public static boolean isZLatexWordPart(char character)
  {
    return Character.isLetterOrDigit(character) || (character == '_')
        || (character == '?') || (character == '!');
  }

  public static boolean isZUnicodeWordPart(char character)
  {
    return Character.isLetterOrDigit(character) || (character == '?')
        || (character == '!') || (character == '\'');
  }

  public static boolean isZLatexWhitespace(char character)
  {
    return Character.isWhitespace(character);
  }

  public static boolean isZUnicodeWhitespace(char character)
  {
    return Character.isWhitespace(character);
  }

}
