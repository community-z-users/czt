
package net.sourceforge.czt.eclipse.editors.parser;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.outline.CztTreeNode;
import net.sourceforge.czt.eclipse.outline.NodeChildrenVisitor;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.oz.ast.ClassPara;
import net.sourceforge.czt.parser.util.CztError;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Oper;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSect;

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

  private CztTreeNode root_;

  private SectionManager manager_;

  private Spec spec_;

  private Map<Term, Position> fTermPositionMap = new HashMap<Term, Position>();

  private Selector fTermSelector;

  private Map<ZName, NameInfo> fNameInfoMap = new HashMap<ZName, NameInfo>();

  private static Visitor<Term[]> getNodeChildrenVisitor_ = new NodeChildrenVisitor();

  public ParsedData(Object source)
  {
    source_ = source;
  }

  public void addData(Spec spec, SectionManager manager, IDocument document)
  {
    spec_ = spec;
    manager_ = manager;
    fTermSelector = new Selector(spec);
    resetTermPositionMap(spec, document);
    //		outputRanges(spec);
    //		outputMap(this.fTermPositionMap);
    //		outputTypeAnns(spec);
    setOutlineTree(spec, document);
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
  
  /**
   * for testing only
   * @param term
   */
  private void outputTypeAnns(Term term)
  {
    if (term != null) {
      //System.out.println("1. term.class -- " + term.getClass());
      TypeAnn typeAnn = (TypeAnn) term.getAnn(TypeAnn.class);
      //System.out.println("2. TypeAnn.value = " + String.valueOf(typeAnn));
      if (typeAnn != null) {
        //System.out.println("3. value: " + String.valueOf(typeAnn.getType()));
        //if (typeAnn.getType() != null) {
        //  System.out
        //      .println("4. NonNullValue: " + typeAnn.getType().toString());
        //}
      }

      for (Object child : term.getChildren()) {
        if (child != null)
          if (child instanceof Term)
            outputTypeAnns((Term) child);
      }
    }
  }

  /** for testing only
   * @param spec
   */
  private void outputRanges(Object obj)
  {
    if (obj == null) {
      //System.out.println("null object");
      return;
    }
    //System.out.println("Object: " + obj.getClass());
    if (obj instanceof Term) {
      Position pos = getRangeOfTerm((Term) obj);
      /*
      if (pos != null) {
        System.out
            .println("(" + pos.getOffset() + ", " + pos.getLength() + ")");
      }
      else {
        System.out.println("null");
      }
      */
      Object[] children = ((Term) obj).getChildren();
      for (int i = 0; i < children.length; i++) {
        // System.out.print("" + i + ".    ");
        outputRanges(children[i]);
      }
    }
  }

  /**
   * for testing only
   * @param map
   */
  private void outputMap(Map<Term, Position> map)
  {
    System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
    System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
    Set set = map.keySet();
    Iterator iter = set.iterator();
    while (iter.hasNext()) {
      System.out.println();
      Term term = (Term) iter.next();
      Position pos = map.get(term);
      System.out.println("Term.getClass: " + term.getClass());
      System.out.println("Term.position: (" + pos.getOffset() + ", "
          + (pos.getOffset() + pos.getLength() - 1) + ")");
    }
    System.out.println();
    System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
    System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
  }

  public SectionManager getSectionManager()
  {
    return this.manager_;
  }

  public CztTreeNode getRoot()
  {
    return this.root_;
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

  public Map<Term, Position> getTermPositionMap()
  {
    return fTermPositionMap;
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

  private void setOutlineTree(Spec spec, IDocument document)
  {
    root_ = new CztTreeNode(source_, spec);
    root_.addAllChildren(getChildrenNodes(spec, document));
  }

  private List<CztTreeNode> getChildrenNodes(Term term, IDocument document)
  {
    List<CztTreeNode> childrenNodes = new ArrayList<CztTreeNode>();
    Term[] children = term.accept(getNodeChildrenVisitor_);

    for (Term child : children) {
      CztTreeNode childNode = createTreeNode(child, document);
      if (childNode == null)
        continue;
      childNode.addAllChildren(getChildrenNodes(child, document));
      childrenNodes.add(childNode);
    }
    return childrenNodes;
  }

  private CztTreeNode createTreeNode(Term term, IDocument document)
  {
    if (term == null)
      return null;
    
    if (term instanceof Spec) {
      // not displayed in Outline, so no Position required
      return new CztTreeNode(source_, term);
    }
    if (term instanceof ZSect) {
      Position range = getPosition(term);
      return new CztTreeNode(source_, term, range);
    }
    else if (term instanceof GivenPara) {
      Position range = getPosition(term);
      Position namePosition = getNamePosition(((GivenPara) term).getNames());
      if (namePosition != null)
        return new CztTreeNode(source_, term, range, namePosition);
      
      return new CztTreeNode(source_, term, range, range);
    }
    else if (term instanceof AxPara) {
      Position range = getPosition(term);
      AxPara axPara = (AxPara) term;
      ZDeclList declList = axPara.getZSchText().getZDeclList();
      Position namePosition = null;
      for (int i = 0; i < declList.size(); i++) {
        Decl decl = declList.get(i);
        if (decl instanceof ConstDecl) {
          namePosition = getPosition(((ConstDecl)decl).getZName());
        }
        else if (decl instanceof VarDecl) {
          namePosition = getNamePosition(((VarDecl)decl).getName());
        }
        if (namePosition != null)
          return new CztTreeNode(source_, term, range, namePosition);
      }
      
      return new CztTreeNode(source_, term, range, range);
    }
    else if (term instanceof FreePara) {
      Position range = getPosition(term);
      Position namePosition = null;
      ZFreetypeList list = (ZFreetypeList)((FreePara)term).getFreetypeList();
      for (int i = 0; i < list.size(); i++) {
        Freetype type = list.get(i);
        namePosition = getPosition(type.getZName());
        if (namePosition != null)
          return new CztTreeNode(source_, term, range, namePosition);
      }
      
      return new CztTreeNode(source_, term, range, range);
    }
    else if (term instanceof ConjPara) {
      Position range = getPosition(term);
      Position namePosition = getNamePosition(((ConjPara)term).getZNameList());
      if (namePosition != null)
        return new CztTreeNode(source_, term, range, namePosition);
      
      return new CztTreeNode(source_, term, range, range);
    }
    else if (term instanceof OptempPara) {
      Position range = getPosition(term);
      Position namePosition = null;
      OptempPara optempPara = (OptempPara) term;
      ListTerm<Oper> operList = optempPara.getOper();
      for (int i = 0; i < operList.size(); i++) {
        Oper oper = operList.get(i);
        namePosition = getPosition(oper);
        if (namePosition != null)
          return new CztTreeNode(source_, term, range, namePosition);
      }
      
      return new CztTreeNode(source_, term, range, range);
    }
    else if (term instanceof ConstDecl) {
      Position range = getPosition(term);
      Position namePosition = getPosition(((ConstDecl) term).getZName());
      return new CztTreeNode(source_, term, range, namePosition);
    }
    else if (term instanceof VarDecl) {
      Position range = getPosition(term);
      Position namePosition = getNamePosition(((VarDecl) term).getName());
      return new CztTreeNode(source_, term, range, namePosition);
    }
    /************** Object-Z nodes ***********************/
    // TODO: add more kinds of Object-Z nodes here
    else if (term instanceof ClassPara) {
      ClassPara cpara = (ClassPara) term;
      Position range = getPosition(term);
      Position namePosition = getPosition(cpara.getName());
      return new CztTreeNode(source_, term, range, namePosition);
    }

    return null;
  }

  private Position getNamePosition(ZNameList nameList)
  {
    int start = -1;
    int end = -1;
    int index;
    for (index = 0; index < nameList.size(); index++) {
      if (start > -1)
        break;
      Position pos = getPosition(nameList.get(index));
      if (pos != null) {
        start = pos.getOffset();
        end = start + pos.getLength() - 1;
      }
    }
    if (start < 0)
      return null;
    for (; index < nameList.size(); index++) {
      Position pos = getPosition(nameList.get(index));
      if (pos != null)
        end = pos.getOffset() + pos.getLength() - 1;
    }

    if ((start > -1) && (end >= start))
      return new Position(start, end - start + 1);

    return null;
  }

  private Position getPosition(Term term)
  {
    if (term == null)
      return null;
    
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
    if (locAnn != null) {
      BigInteger start = locAnn.getStart();
      BigInteger length = locAnn.getLength();
      //if (term instanceof ZDeclName) {
      //  System.out.println("DeclName-----" + ((ZDeclName)term).getWord());
      //}
      //System.out.println("Position: ----" + start + ", " + length);
      if ((start != null) && (length != null))
        return new Position(start.intValue(), length.intValue());
    }
    return this.fTermPositionMap.get(term);
  }

  private void resetTermPositionMap(Spec spec, IDocument document)
  {
    Object[] children = spec.getChildren();
    int start = 0;
    int end = document.getLength() - 1;

    this.fTermPositionMap.clear();
    this.fTermPositionMap.putAll(getTermPositionMapFromChildren(children,
        document, start, end));
  }

  private Map<Term, Position> getTermPositionMapFromChildren(Object[] terms,
      IDocument document, int defaultStart, int defaultEnd)
  {
    Map<Term, Position> map = new HashMap<Term, Position>();

    int next = -1;
    int prevEnd = -1; // the offset of previous term's end
    int nextStart = -1; // the offset of next term's start
    //		System.out.println("terms.length: " + terms.length);

    for (int current = 0; current < terms.length;) {
      next = current + 1;
      //			System.out.println("next: " + next);
      //			if (terms[current] != null)
      //				System.out.println("current.class: " + current + ". "+ terms[current].getClass().toString());
      if (terms[current] == null) {
      }
      else if (terms[current] instanceof Term) {
        // get the range directly
        Position range = getRangeOfTerm((Term) terms[current]);
        if (range != null) {
          //					System.out.println("Position: (" + range.getOffset() + ", " + (range.getOffset() + range.getLength() - 1) + ")");
          map.put((Term) terms[current], range);
          nextStart = range.getOffset() + range.getLength();
          //if (!(terms[current] instanceof ZRefName)) {
          if (!(terms[current] instanceof ZName)) {
            map.putAll(getTermPositionMapFromChildren(((Term) terms[current])
                .getChildren(), document, range.getOffset(), range.getOffset()
                + range.getLength() - 1));
          }
        }
        else {
          // get the start offset
          int start;

          if (nextStart > -1) {
            //						System.out.println("start = nextStart");
            start = nextStart;
          }
          else if (prevEnd > -1) {
            //						System.out.println("start = prevEnd - 1");
            start = prevEnd + 1;
          }
          else {
            start = getRangeStart((Term) terms[current], document);
            if (start < 0) {
              //							System.out.println("start = defaultStart");
              start = defaultStart;
            }
            else {
              //							System.out.println("start = getRangeStart");
            }
          }

          int end = -1;
          nextStart = -1;

          int length = getTermLength((Term) terms[current]);
          if (length > 0)
            end = start + length - 1;
          else {
            end = getChildrenEnd((Term) terms[current]);
            if (end < 0) {
              for (; next < terms.length; next++) {
                //								System.out.println("next inside: " + next);
                //								System.out.println("next inside class: " + terms[next].getClass());
                if (terms[next] instanceof Term) {
                  nextStart = getRangeStart((Term) terms[next], document);
                  if (nextStart > -1) {
                    //										System.out.println("end = nextStart - 1");
                    end = nextStart - 1;
                    break;
                  }
                }
              }
            }
            else {
              //							System.out.println("end = getChildrenEnd");
            }
          }

          if (end < 0) {
            //						System.out.println("end = defaultEnd");
            end = defaultEnd;
          }

          //					System.out.println("Position: (" + start + ", " + end + ")");
          if (end >= start) {
            map
                .put((Term) terms[current],
                    new Position(start, end - start + 1));
            //if (!(terms[current] instanceof ZRefName)) {
            if (!(terms[current] instanceof ZName)) {  
              map.putAll(getTermPositionMapFromChildren(((Term) terms[current])
                  .getChildren(), document, start, end));
            }
          }
        }
      }

      current = next;
    }

    return map;
  }

  /**
   * 
   * @param term the term to get the range of
   * @return
   */
  private Position getRangeOfTerm(Term term)
  {
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);

    if (locAnn != null) {
      BigInteger rangeStart = locAnn.getStart();
      BigInteger rangeLength = locAnn.getLength();
      if ((rangeStart != null) && (rangeLength != null))
        return new Position(rangeStart.intValue(), rangeLength.intValue());
    }

    return null;
  }

  private int getRangeStart(Term term, IDocument document)
  {
    //		System.out.println("term.class: " + term.getClass());
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);

    if (locAnn != null) {
      BigInteger start = locAnn.getStart();
      if (start != null) {
        //				System.out.println("locAnn.getStart: " + start);
        return start.intValue();
      }

      try {
        if ((locAnn.getLine() != null) && (locAnn.getCol() != null)) {
          int line = locAnn.getLine().intValue();
          int column = locAnn.getCol().intValue();

          //				System.out.println("line: " + line);
          //				System.out.println("column: " + column);
          //				System.out.println("lineoffset: " + document.getLineOffset(line));
          return document.getLineOffset(line) + column;
        }
      } catch (BadLocationException ble) {
        return -1;
      }
    }
    else {
      Object[] objects = term.getChildren();
      int start = -1;
      for (int i = 0; i < objects.length; i++) {
        if (objects[i] instanceof Term)
          start = getRangeStart((Term) objects[i], document);
        if (start > -1)
          return start;
      }
    }

    return -1;
  }

  private int getTermLength(Term term)
  {
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);

    if (locAnn != null) {
      BigInteger length = locAnn.getLength();
      if (length != null)
        return length.intValue();
    }

    return -1;
  }

  private int getChildrenEnd(Term term)
  {
    //		System.out.println("term.class: " + term.getClass());
    Object[] children = term.getChildren();
    int end = -1;
    for (int i = children.length - 1; i >= 0; i--)
      if (children[i] instanceof Term) {
        LocAnn locAnn = (LocAnn) ((Term) children[i]).getAnn(LocAnn.class);
        if (locAnn != null) {
          BigInteger start = locAnn.getStart();
          BigInteger length = locAnn.getLength();
          if ((start != null) && (length != null)) {
            //						System.out.println("locAnn.getStart: " + start);
            end = start.intValue() + length.intValue() - 1;
            if (end < 0)
              end = getChildrenEnd((Term) children[i]);
          }
        }
        else
          end = getChildrenEnd((Term) children[i]);

        if (end > -1)
          break;
      }

    return end;
  }
}
