
package net.sourceforge.czt.modeljunit.gui;

/*
 * This class is for generating indented Java code.
 *
 * Every line has an indentation at the beginning of the line.
 * The wrap method calculates the indentation and uses the shrink() or
 * expand() methods to adjust the indentation by checking whether the
 * input string includes '{' or '}'.
 *
 * @author rong ID : 1005450 5th Aug 2007
 */

public class Indentation
{
  private static final String INDENTATION = "  ";

  private static String m_strIndentation = new String();

  public static final String SEP = System.getProperty("line.separator");

  protected static void expand()
  {
    m_strIndentation = m_strIndentation.concat(INDENTATION);
  }

  protected static void shrink()
  {
    m_strIndentation = m_strIndentation.substring(0, m_strIndentation.length()
        - INDENTATION.length());
  }

  /** This adds the current indentation prefix to str.
   *  As a side effect, it also adjusts the current indentation level
   *  up by one if str contains a '{' character, or down by one if
   *  it contains a '}' character.
   *
   * @param str The line to be indented.  Should not contain newlines.
   * @return    The indented line.
   */
  public static String indent(String str)
  {
    int front = str.indexOf('{');
    int rear = str.indexOf('}');
    if (front >= 0) {
      str = m_strIndentation + str;
      expand();
    }
    if (rear >= 0) {
      shrink();
      str = m_strIndentation + str;
    }
    if (front < 0 && rear < 0)
      str = m_strIndentation + str;
    str += SEP;
    return str;
  }
}
