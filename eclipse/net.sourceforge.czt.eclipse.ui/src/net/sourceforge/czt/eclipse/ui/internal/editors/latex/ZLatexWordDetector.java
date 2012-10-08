/**
 * Created on 2005-10-19
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.latex;

import net.sourceforge.czt.eclipse.ui.internal.editors.ZCharacter;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * @author Chengdong Xu
 */
public class ZLatexWordDetector implements IWordDetector
{

  /**
   * Method declared on IWordDetector.
   * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
   */
  public boolean isWordStart(char character)
  {
    return ZCharacter.isZLaTexWordStart(character);
  }

  /**
   * Method declared on IWordDetector.
   * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
   */
  public boolean isWordPart(char character)
  {
    return ZCharacter.isZLaTexWordPart(character);
  }
}