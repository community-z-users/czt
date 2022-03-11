/**
 * Created on 2005-10-19
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.unicode;

import org.eclipse.jface.text.rules.IWordDetector;

import net.sourceforge.czt.eclipse.ui.internal.editors.ZCharacter;

/**
 * @author Chengdong Xu
 */
public class ZUnicodeWordDetector implements IWordDetector
{
  /**
   * Method declared on IWordDetector.
   * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
   */
  public boolean isWordStart(char character)
  {
    return ZCharacter.isZUnicodeWordStart(character);
  }

  /**
   * Method declared on IWordDetector.
   * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
   */
  public boolean isWordPart(char character)
  {
    return ZCharacter.isZUnicodeWordPart(character);
  }
}
