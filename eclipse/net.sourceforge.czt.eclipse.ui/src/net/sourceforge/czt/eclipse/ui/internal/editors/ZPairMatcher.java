/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors;

import java.util.Stack;

import net.sourceforge.czt.eclipse.ui.CztUIPlugin;
import net.sourceforge.czt.eclipse.ui.editors.IZPartitions;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITypedRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ICharacterPairMatcher;

/**
 * Matching pairs of brackets
 * @author Chengdong Xu
 */
public class ZPairMatcher implements ICharacterPairMatcher
{

  protected char[] fPairs;

  protected IDocument fDocument;

  protected int fOffset;
  
  protected ITypedRegion fPartition;

  protected int fStartPos;

  protected int fEndPos;

  protected int fAnchor;

  /**
   * 
   */
  public ZPairMatcher(char[] pairs)
  {
    fPairs = pairs;
  }

  /**
   * @see org.eclipse.jface.text.source.ICharacterPairMatcher#match(org.eclipse.jface.text.IDocument, int)
   */
  public IRegion match(IDocument document, int offset)
  {
    if (document == null || offset < 0)
      return null;
    
    fDocument = document;
    fOffset = offset;
    fPartition = getPartition(document, Math.max(fOffset - 1, 0));
    
    if (fPartition != null && matchPairsAt() && fStartPos != fEndPos)
      return new Region(fStartPos, fEndPos - fStartPos + 1);

    return null;
  }

  /**
   * @see org.eclipse.jface.text.source.ICharacterPairMatcher#getAnchor()
   */
  public int getAnchor()
  {
    return fAnchor;
  }

  /**
   * @see org.eclipse.jface.text.source.ICharacterPairMatcher#dispose()
   */
  public void dispose()
  {
    clear();
    fDocument = null;
  }

  /**
   * @see org.eclipse.jface.text.source.ICharacterPairMatcher#clear()
   */
  public void clear()
  {
  }

  protected boolean matchPairsAt()
  {

    int i;
    int pairIndex1 = fPairs.length;
    int pairIndex2 = fPairs.length;

    fStartPos = -1;
    fEndPos = -1;

    // get the char preceding the start position
    try {

      char prevChar = fDocument.getChar(Math.max(fOffset - 1, 0));
      // search for opening peer character next to the activation point
      for (i = 0; i < fPairs.length; i = i + 2) {
        if (prevChar == fPairs[i]) {
          fStartPos = fOffset - 1;
          pairIndex1 = i;
        }
      }

      // search for closing peer character next to the activation point
      for (i = 1; i < fPairs.length; i = i + 2) {
        if (prevChar == fPairs[i]) {
          fEndPos = fOffset - 1;
          pairIndex2 = i;
        }
      }
      
      if (fEndPos > -1) {
        fAnchor = RIGHT;
        fStartPos = searchForOpeningPeer(fEndPos, fPairs[pairIndex2 - 1],
            fPairs[pairIndex2], fDocument);
        if (fStartPos > -1)
          return true;
        else
          fEndPos = -1;
      }
      else if (fStartPos > -1) {
        fAnchor = LEFT;
        fEndPos = searchForClosingPeer(fStartPos, fPairs[pairIndex1],
            fPairs[pairIndex1 + 1], fDocument);
        if (fEndPos > -1)
          return true;
        else
          fStartPos = -1;
      }

    } catch (BadLocationException x) {
    }

    return false;
  }

  protected int searchForClosingPeer(int offset, char openingPeer,
      char closingPeer, IDocument document) throws BadLocationException
  {
    Stack<Character> foundBrackets = new Stack<Character>();
    for (++offset; offset < fPartition.getOffset() + fPartition.getLength(); offset++) {
      char currentChar = document.getChar(offset);
      for (int i = 0; i < fPairs.length; i++) {
        // check if it is a bracket
        if (currentChar != fPairs[i])
          continue;
        // check if it is an opening peer
        if (i % 2 == 0) {
          foundBrackets.push(Character.valueOf(currentChar));
          break;
        }
        // it is an closing peer
        if (foundBrackets.empty()) {
          if (currentChar == closingPeer)
            return offset;
          else
            return -1;
        }
        else {
          if (Character.valueOf(fPairs[i-1]).equals(foundBrackets.pop()))
            break;
          foundBrackets.clear();
          return -1;
        }  
      }
    }
    
    return -1;
  }

  protected int searchForOpeningPeer(int offset, char openingPeer,
      char closingPeer, IDocument document) throws BadLocationException
  {
    Stack<Character> foundBrackets = new Stack<Character>();
    
    for (--offset; offset > fPartition.getOffset() - 1; offset--) {
      char currentChar = document.getChar(offset);
      for (int i = 0; i < fPairs.length; i++) {
        // check if it is a bracket
        if (currentChar != fPairs[i])
          continue;
        // check if it is an closing peer
        if (i % 2 == 1) {
          foundBrackets.push(Character.valueOf(currentChar));
          break;
        }
        // it is an opening peer
        if (foundBrackets.empty()) {
          if (currentChar == openingPeer)
            return offset;
          else
            return -1;
        }
        else {
          if (Character.valueOf(fPairs[i+1]).equals(foundBrackets.pop()))
            break;
          foundBrackets.clear();
          return -1;
        }
      }
    }
    
    return -1;
  }

  protected ITypedRegion getPartition(IDocument document, int offset)
  {
    return CztUIPlugin.getDefault().getCZTTextTools().getPartition(document, offset, IZPartitions.Z_PARTITIONING);
  }
}
