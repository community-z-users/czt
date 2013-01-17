package net.sourceforge.czt.eclipse.core.document;

import java.math.BigInteger;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.text.Position;
import net.sourceforge.czt.z.ast.LocAnn;

public class TermPositionProvider implements IPositionProvider<Term>
{

  private final IDocument document;
  
  public TermPositionProvider(IDocument document)
  {
    this.document = document;
  }

  @Override
  public Position getPosition(Term term)
  {
    if (term == null) {
      return null;
    }
    
    BigInteger startPos = getStart(term, document);
    BigInteger endPos = getEnd(term);
    
    if (startPos == null) {
      return null;
    }
    
    if (endPos == null) {
      // cannot find end position, though found start position (e.g. via line/col)
      // use start as end - will be 0-length marker, still better than nothing
      endPos = startPos;
    }
    
    int start = startPos.intValue();
    int end = endPos.intValue();
    
    int length = end - start;
    if (start < 0 || end < 0 || length < 0) {
      // somehow invalid (happens when the same terms are reused in AST and therefore they have
      // strange LocAnns associated. For example, this happens for RefExpr, where its ZName is reused.
      // For now, ignore this
      // TODO update RefExpr location generation?
      return null;
    }
    
    return new Position(start, length);
  }
  
  private BigInteger getStart(Term term, IDocument document)
  {
    
    LocAnn locAnn = term.getAnn(LocAnn.class);
    if (locAnn != null) {
      
      if (locAnn.getStart() != null) {
        return locAnn.getStart();
      }
      
      // check if document and line/col is available
      if (document != null && locAnn.getLine() != null && locAnn.getCol() != null) {
        try {
          return BigInteger.valueOf(
        		  // the LocAnn.getLine() apparently is 0-based, so no need to remove 1
              document.getLineOffset(locAnn.getLine().intValue())// - 1)
                + locAnn.getCol().intValue());
        }
        catch (BadLocationException e) {}
      }
    }
    
    // if the term itself does not have a proper location annotation, check its children depth-first
    BigInteger min = null;
    for (Object child : term.getChildren()) {
      if (child instanceof Term) {
        BigInteger start = getStart((Term) child, document);
        if (start != null) {
          
          if (min == null) {
            min = start;
          } else {
            min = min.min(start);
          }
        }
      }
    }
    
    return min;
  }
  
  private BigInteger getEnd(Term term)
  {
    
    LocAnn locAnn = term.getAnn(LocAnn.class);
    if (locAnn != null) {
      
      if (locAnn.getEnd() != null) {
        return locAnn.getEnd();
      }
    }
    
    // if the term itself does not have a proper location annotation, 
    // check its children depth-first
    BigInteger max = null;
    for (Object child : term.getChildren()) {
      if (child instanceof Term) {
        BigInteger end = getEnd((Term) child);
        if (end != null) {
          
          if (max == null) {
            max = end;
          } else {
            max = max.max(end);
          }
        }
      }
    }
    
    return max;
    
  }

}
