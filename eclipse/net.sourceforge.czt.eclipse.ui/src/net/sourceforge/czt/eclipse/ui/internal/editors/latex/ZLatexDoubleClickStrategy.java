/**
 * A ZLatexDoubleClickStrategy
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.latex;

import net.sourceforge.czt.eclipse.ui.internal.editors.ZCharacter;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextDoubleClickStrategy;
import org.eclipse.jface.text.ITextViewer;

/**
 * @author Chengdong Xu
 * 
 */
public class ZLatexDoubleClickStrategy implements ITextDoubleClickStrategy
{

  protected ITextViewer fText;

  protected int fPos;

  protected int fStartPos;

  protected int fEndPos;

  protected ZLatexPairMatcher fPairMatcher = new ZLatexPairMatcher(ZCharacter.BRACKETS_LATEX);

  /**
   * Create a ZLatexDoubleClickStrategy
   */
  public ZLatexDoubleClickStrategy()
  {
    super();
  }

  /**
   * Method declared on ITextDoubleClickStrategy
   * 
   * @see org.eclipse.jface.text.ITextDoubleClickStrategy#doubleClicked(org.eclipse.jface.text.ITextViewer)
   */
  public void doubleClicked(ITextViewer textViewer)
  {
    fPos = textViewer.getSelectedRange().x;

    if (fPos < 0)
      return;

    fText = textViewer;
    IDocument document = textViewer.getDocument();

    IRegion region = fPairMatcher.match(document, fPos);
    int startLength = fPairMatcher.getStartLength();
    int endLength = fPairMatcher.getEndLength();
    if (region != null && region.getLength() >= startLength + endLength) {
      textViewer.setSelectedRange(region.getOffset() + startLength,
          region.getLength() - startLength - endLength);
    }
    else {
      selectWord();
    }
  }

  /**
   * Select the word at the current selection.
   */
  protected void selectWord()
  {
    if (matchWord()) {
      if (fStartPos == fEndPos)
        fText.setSelectedRange(fStartPos, 1);
      else
        fText.setSelectedRange(fStartPos, fEndPos - fStartPos + 1);
    }
  }

  /**
   * Select the word at the current selection location. Return
   * <code>true</code> if successful, <code>false</code> otherwise.
   * 
   * @return <code>true</code> if a word can be found at the current
   *         selection location, <code>false</code> otherwise
   */
  protected boolean matchWord()
  {

    IDocument document = fText.getDocument();

    try {

      int pos = fPos;
      char c;

      c = document.getChar(pos);
      if (ZCharacter.isZLaTexWhitespace(c))
        return false;

      while (pos >= 0) {
        c = document.getChar(pos);
        if (!ZCharacter.isZLaTexWordPart(c)) {
          if (ZCharacter.isZLaTexWordStart(c))
            --pos;
          else if (pos == fPos)
            return false;
          break;
        }
        --pos;
      }

      fStartPos = pos + 1;

      pos = fPos + 1;
      int length = document.getLength();

      while (pos < length) {
        c = document.getChar(pos);
        if (!ZCharacter.isZLaTexWordPart(c))
          break;
        ++pos;
      }

      fEndPos = pos - 1;

      return true;

    } catch (BadLocationException x) {
    }

    return false;
  }
}
