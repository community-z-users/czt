
package net.sourceforge.czt.eclipse.editors.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZName;
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
  
  private IPositionProvider<Term> posProvider;

  private Selector fTermSelector;

  private Map<ZName, NameInfo> fNameInfoMap = new HashMap<ZName, NameInfo>();


  public ParsedData(Object source)
  {
    source_ = source;
  }

  public void setData(Spec spec, SectionManager manager, IDocument document)
  {
    spec_ = spec;
    posProvider = new TermPositionProvider(document);
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
    return posProvider.getPosition(term);
  }

}
