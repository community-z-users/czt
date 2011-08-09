
package net.sourceforge.czt.eclipse.editors.parser;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZName;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;

/**
 * @author Chengdong Xu
 */
public class ParsedData
{
  private Object source_;
  
  private List<CztError> fErrorList = new ArrayList<CztError>();

  private SectionManager manager_;

  private Spec spec_;
  
  private IDocument document_;

  private Selector fTermSelector;

  private Map<ZName, NameInfo> fNameInfoMap = new HashMap<ZName, NameInfo>();


  public ParsedData(Object source)
  {
    source_ = source;
  }

  public void addData(Spec spec, SectionManager manager, IDocument document)
  {
    spec_ = spec;
    document_ = document;
    manager_ = manager;
    fTermSelector = new Selector(spec);
    //		outputTypeAnns(spec);
    fNameInfoMap = NameInfoResolver.resolve(spec, manager);
  }
  
  public void setErrors(List<CztError> errors)
  {
    fErrorList = errors;
  }
  
  public List<CztError> getErrors()
  {
    return fErrorList;
  }
  
//  /**
//   * for testing only
//   * @param term
//   */
//  private void outputTypeAnns(Term term)
//  {
//    if (term != null) {
//      //System.out.println("1. term.class -- " + term.getClass());
//      TypeAnn typeAnn = term.getAnn(TypeAnn.class);
//      //System.out.println("2. TypeAnn.value = " + String.valueOf(typeAnn));
//      if (typeAnn != null) {
//        //System.out.println("3. value: " + String.valueOf(typeAnn.getType()));
//        //if (typeAnn.getType() != null) {
//        //  System.out
//        //      .println("4. NonNullValue: " + typeAnn.getType().toString());
//        //}
//      }
//
//      for (Object child : term.getChildren()) {
//        if (child != null)
//          if (child instanceof Term)
//            outputTypeAnns((Term) child);
//      }
//    }
//  }
//
//  /** for testing only
//   * @param spec
//   */
//  private void outputRanges(Object obj)
//  {
//    if (obj == null) {
//      //System.out.println("null object");
//      return;
//    }
//    //System.out.println("Object: " + obj.getClass());
//    if (obj instanceof Term) {
//      Position pos = getPosition((Term) obj);
//      /*
//      if (pos != null) {
//        System.out
//            .println("(" + pos.getOffset() + ", " + pos.getLength() + ")");
//      }
//      else {
//        System.out.println("null");
//      }
//      */
//      Object[] children = ((Term) obj).getChildren();
//      for (int i = 0; i < children.length; i++) {
//        // System.out.print("" + i + ".    ");
//        outputRanges(children[i]);
//      }
//    }
//  }

  public SectionManager getSectionManager()
  {
    return this.manager_;
  }


  public Object getSource()
  {
    return source_;
  }

  public Spec getSpec()
  {
    return spec_;
  }

  public Map<ZName, NameInfo> getNameInfoMap()
  {
    return fNameInfoMap;
  }

  public Selector getTermSelector()
  {
    if (fTermSelector == null)
      fTermSelector = new Selector(spec_);
    
    return fTermSelector;
  }
  
  public Selector createTermSelector()
  {
    return new Selector(spec_);
  }

  public Position getTermPosition(Term term)
  {
    return getPosition(term);
  }


  private Position getPosition(Term term)
  {
    if (term == null) {
      return null;
    }
    
    BigInteger startPos = getStart(term, document_);
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
              document.getLineOffset(locAnn.getLine().intValue() - 1)
                + locAnn.getCol().intValue());
        }
        catch (BadLocationException e) {}
      }
    }
    
    // if the term itself does not have a proper location annotation, check its children depth-first
    for (Object child : term.getChildren()) {
      if (child instanceof Term) {
        BigInteger start = getStart((Term) child, document);
        if (start != null) {
          return start;
        }
      }
    }
    
    return null;
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
    // check its children depth-first, starting from the end
    Object[] children = term.getChildren();
    for (int index = children.length - 1; index >= 0; index--) {
      Object child = children[index];
      
      if (child instanceof Term) {
        BigInteger end = getEnd((Term) child);
        if (end != null) {
          return end;
        }
      }
    }
    
    return null;
    
  }

}
