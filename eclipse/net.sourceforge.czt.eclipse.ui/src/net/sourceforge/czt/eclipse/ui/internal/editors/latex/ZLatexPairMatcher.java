/**
 * 
 */

package net.sourceforge.czt.eclipse.ui.internal.editors.latex;

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
public class ZLatexPairMatcher implements ICharacterPairMatcher
{

  protected String[] fPairs;

  protected IDocument fDocument;

  protected int fOffset;

  protected ITypedRegion fPartition;

  protected int fStartPos;

  protected int fEndPos;

  protected int fAnchor;

  protected int fLengthOfStart;

  protected int fLengthOfEnd;

  /**
   * 
   */
  public ZLatexPairMatcher(String[] pairs)
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
    
    fStartPos = -1;
    fEndPos = -1;

    int foundIndex = -1;
    int foundLength = -1;
    try {
      // find the bracket matching at the position
      for (int i = 0; i < fPairs.length; i++) {
        int length = fPairs[i].length();
        if (length > foundLength && fOffset - length > -1
            && fPairs[i].equals(fDocument.get(fOffset - length, length))) {
          foundIndex = i;
          foundLength = length;
        }
      }
      
      if (foundIndex == -1)
        return false;
      
      if (foundIndex % 2 == 0) {
        fStartPos = fOffset - foundLength;
        fLengthOfStart = foundLength;
        fAnchor = LEFT;
        
        fEndPos = searchForClosingPeer(fOffset,
            fPartition.getOffset() + fPartition.getLength() - 1,
            fPairs[foundIndex],
            fPairs[foundIndex + 1],
            fDocument);
        
        if (fEndPos > -1)
          return true;
        else
          fStartPos = -1;
      }
      else {
        fEndPos = fOffset - 1;
        fLengthOfEnd = foundLength;
        fAnchor = RIGHT;
        
        fStartPos = searchForOpeningPeer(fPartition.getOffset(),
            fOffset - foundLength - 1,
            fPairs[foundIndex - 1],
            fPairs[foundIndex],
            fDocument);
        
        if (fStartPos > -1)
          return true;
        else
          fEndPos = -1;
      }
    } catch (BadLocationException x) {
    }

    return false;
  }

  protected int searchForClosingPeer(int start, int end, String openingPeer,
      String closingPeer, IDocument document) throws BadLocationException
  {
    Stack<String> foundBrackets = new Stack<String>();
    for (int offset = start; offset < end + 1; offset++) {
      int foundIndex = -1;
      int foundLength = -1;
      for (int i = 0; i < fPairs.length; i++) {
        int length = fPairs[i].length();
        if (length > foundLength && offset + length -1 <= end
            && fPairs[i].equals(fDocument.get(offset, length))) {
          foundIndex = i;
          foundLength = length;
        }
      }
      
      // check if a bracket is found
      if (foundIndex == -1)
        continue;
      
      // check if it is an opening peer
      if (foundIndex % 2 == 0) {
        foundBrackets.push(fPairs[foundIndex]);
        offset += foundLength - 1;
        continue;
      }
      
      // it is a closing peer
      if (foundBrackets.empty()) {
        if (fPairs[foundIndex].equals(closingPeer)) {
          fLengthOfEnd = foundLength;
          return offset + foundLength - 1;
        }
        else
          return -1;
      }
      else {
        if (fPairs[foundIndex - 1].equals(foundBrackets.pop())) {
          offset += foundLength - 1;
          continue;
        }
        else {
          foundBrackets.clear();
          return -1;
        }
      }
    }

    return -1;
  }

  protected int searchForOpeningPeer(int start, int end, String openingPeer,
      String closingPeer, IDocument document) throws BadLocationException
  {
    Stack<String> foundBrackets = new Stack<String>();
    for (int offset = end; offset > start - 1; offset--) {
      int foundIndex = -1;
      int foundLength = -1;
      for (int i = 0; i < fPairs.length; i++) {
        int length = fPairs[i].length();
        if (length > foundLength && offset - length + 1 >= start
            && fPairs[i].equals(fDocument.get(offset - length + 1, length))) {
          foundIndex = i;
          foundLength = length;
        }
      }
      
      // check if a bracket is found
      if (foundIndex == -1)
        continue;
      
      // check if it is a closing peer
      if (foundIndex % 2 == 1) {
        foundBrackets.push(fPairs[foundIndex]);
        offset -= foundLength - 1;
        continue;
      }
      
      // it is an opening peer
      if (foundBrackets.empty()) {
        if (fPairs[foundIndex].equals(openingPeer)) {
          fLengthOfStart = foundLength;
          return offset - foundLength + 1;
        }
        else
          return -1;
      }
      else {
        if (fPairs[foundIndex + 1].equals(foundBrackets.pop())) {
          offset -= foundLength - 1;
          continue;
        }
        else {
          foundBrackets.clear();
          return -1;
        }
      }
    }

    return -1;
  }

  protected ITypedRegion getPartition(IDocument document, int offset)
  {
    return CztUIPlugin.getDefault().getCZTTextTools().getPartition(document,
        offset, IZPartitions.Z_PARTITIONING);
  }

  public int getStartLength()
  {
    return fLengthOfStart;
  }

  public int getEndLength()
  {
    return fLengthOfEnd;
  }
}
