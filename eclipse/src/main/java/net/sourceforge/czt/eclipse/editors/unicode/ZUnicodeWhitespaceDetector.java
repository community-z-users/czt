/**
 * Created on 2005-10-13
 */

package net.sourceforge.czt.eclipse.editors.unicode;

import net.sourceforge.czt.eclipse.editors.ZCharacter;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

/**
 * @author Chengdong Xu
 */
public class ZUnicodeWhitespaceDetector implements IWhitespaceDetector
{

  /* (non-Javadoc)
   * Method declared on IWhitespaceDetector
   * @see org.eclipse.jface.text.rules.IWhitespaceDetector#isWhitespace(char)
   */
  public boolean isWhitespace(char character)
  {
    return ZCharacter.isZLatexWhitespace(character);
  }

}
