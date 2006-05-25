package net.sourceforge.czt.eclipse.editors.parser;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.eclipse.editors.visitor.NodeChildrenVisitor;
import net.sourceforge.czt.eclipse.editors.visitor.NodeDescriptionVisitor;
import net.sourceforge.czt.eclipse.editors.visitor.NodeNameVisitor;
import net.sourceforge.czt.eclipse.outline.CztSegment;
import net.sourceforge.czt.eclipse.outline.Segment;
import net.sourceforge.czt.eclipse.util.Selector;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclNameList;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.ast.ZSect;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.Position;

/**
 * @author Chengdong Xu
 */
public class ParsedData {
	
	private Object source_;
	private CztSegment root_;
	private SectionManager manager_;
	private Spec spec_;
	private Map<Term, Position> fTermPositionMap = new HashMap<Term, Position>();
	private Selector fTermSelector;
	private List<Triple> triples_ = new ArrayList<Triple>();
	
	private static Visitor<String> getNodeNameVisitor_ = new NodeNameVisitor();

	private static Visitor<String> getNodeDescriptionVisitor_ = new NodeDescriptionVisitor();

	private static Visitor<Term[]> getNodeChildrenVisitor_ = new NodeChildrenVisitor();
	
	public ParsedData(Object source) {
		source_ = source;
		root_ = new CztSegment(source, new Segment(String.valueOf(source)), null);
	}
	
	public void addData(Spec spec, SectionManager manager, IDocument document) {
		this.spec_ = spec;
		this.manager_ = manager;
		this.fTermSelector = new Selector(spec);
		resetTermPositionMap(spec, document);
//		outputRanges(spec);
//		outputMap(this.fTermPositionMap);
//		outputTypeAnns(spec);
		setOutlineTree(spec, document);
		triples_ = TypesFinder.getTypes(spec, manager);
	}

	/**
	 * for testing only
	 * @param term
	 */
	private void outputTypeAnns(Term term) {
		if (term != null) {
			System.out.println("1. term.class -- " + term.getClass());
			TypeAnn typeAnn = (TypeAnn)term.getAnn(TypeAnn.class);
			System.out.println("2. TypeAnn.value = " + String.valueOf(typeAnn));
			if (typeAnn != null) {
				System.out.println("3. value: " + String.valueOf(typeAnn.getType()));
				if (typeAnn.getType() != null)
					System.out.println("4. NonNullValue: " + typeAnn.getType().toString());
			}
			
			for (Object child : term.getChildren()) {
				if (child != null)
					if (child instanceof Term)
						outputTypeAnns((Term)child);
			}
		}
	}
	
	/** for testing only
	 * @param spec
	 */
	private void outputRanges(Object obj) {
		if (obj == null) {
			System.out.println("null object");
			return;
		}
		System.out.println("Object: " + obj.getClass());
		if (obj instanceof Term) {
			Position pos = getRangeOfTerm((Term)obj);
			if (pos != null)
				System.out.println("(" + pos.getOffset() + ", " + pos.getLength() + ")");
			else
				System.out.println("null");
			Object[] children = ((Term)obj).getChildren();
			for (int i = 0; i < children.length; i++) {
				System.out.print("" + i + ".    ");
				outputRanges(children[i]);
			}
		}
	}
	/**
	 * for testing only
	 * @param map
	 */
	private void outputMap(Map<Term, Position> map) {
		System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
		System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
		Set set = map.keySet();
		Iterator iter = set.iterator();
		while(iter.hasNext()) {
			System.out.println();
			Term term = (Term)iter.next();
			Position pos = map.get(term);
			System.out.println("Term.getClass: " + term.getClass());
			System.out.println(
					"Term.position: ("
					+ pos.getOffset()
					+ ", "
					+ (pos.getOffset() + pos.getLength() - 1)
					+ ")");
		}
		System.out.println();
		System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
		System.out.println("|+++++++++++++++++++++++++++++++++++++++++++++++++|");
	}
	
	public SectionManager getSectionManager() {
		return this.manager_;
	}
	
	public CztSegment getRoot() {
		return this.root_;
	}
	
	public Object getSource() {
		return this.source_;
	}
	
	public Spec getSpec() {
		return this.spec_;
	}
	
	public List<Triple> getNameSectTypeTriples() {
		return this.triples_;
	}
	
	public Map<Term, Position> getTermPositionMap() {
		return this.fTermPositionMap;
	}
	
	public Selector getTermSelector() {
		return this.fTermSelector;
	}
	
	public Position getTermPosition(Term term) {
		return getPosition(term);
	}
	
	private void setOutlineTree(Spec spec, IDocument document) {
		root_.addAllChildren(getChildrenNodes(spec, document));
	}
	
	private List<CztSegment> getChildrenNodes(Term term, IDocument document) {
		List<CztSegment> childrenNodes = new ArrayList<CztSegment>();
		for (Term child : term.accept(getNodeChildrenVisitor_)) {
			CztSegment childNode = getTreeNode(child, document);
			if (childNode == null)
				childrenNodes.addAll(getChildrenNodes(child, document));
			else {
				childNode.addAllChildren(getChildrenNodes(child, document));
				childrenNodes.add(childNode);
			}
		}
		return childrenNodes;
	}
	
	private CztSegment getTreeNode(Term term, IDocument document) {
		if (term == null)
			return null;
		if (term instanceof ZSect) {
			Segment segment = new Segment(term.accept(getNodeNameVisitor_), term.accept(getNodeDescriptionVisitor_));
			Position range = getPosition(term);
			return new CztSegment(source_, segment, range);
		}
		else if (term instanceof GivenPara) {
			Segment segment = new Segment(term.accept(getNodeNameVisitor_), term.accept(getNodeDescriptionVisitor_));
			Position range = getPosition(term);
			Position namePosition = getNamePosition(((GivenPara)term).getDeclName());			
			return new CztSegment(source_, segment, range, namePosition);
		}
		else if (term instanceof AxPara) {
			Segment segment = new Segment(term.accept(getNodeNameVisitor_), term.accept(getNodeDescriptionVisitor_));
			Position range = getPosition(term);
			Position namePosition = getNamePosition(((AxPara)term).getDeclName());
			return new CztSegment(source_, segment, range, namePosition);
		}
		else if (term instanceof ConstDecl) {
			Segment segment = new Segment(term.accept(getNodeNameVisitor_), term.accept(getNodeDescriptionVisitor_));
			Position range = getPosition(term);
			Position namePosition = getPosition(((ConstDecl)term).getZDeclName());
			return new CztSegment(source_, segment, range, namePosition);
		}
		else if (term instanceof VarDecl) {
			Segment segment = new Segment(term.accept(getNodeNameVisitor_), term.accept(getNodeDescriptionVisitor_));
			Position range = getPosition(term);
			Position namePosition = getNamePosition(((VarDecl)term).getDeclName());
			return new CztSegment(source_, segment, range, namePosition);
		}
		
		return null;
	}
	
	private Position getNamePosition(ZDeclNameList nameList) {
		int start = -1;
		int end = -1;
		int index;
		for (index = 0; index < nameList.size(); index++) {
			if(start > -1)
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
	
	private Position getPosition(Term term) {
		if (term == null)
			return null;
		LocAnn locAnn = (LocAnn)term.getAnn(LocAnn.class);
		if (locAnn != null) {
			BigInteger start = locAnn.getStart();
			BigInteger length = locAnn.getLength();
			if ((start != null) && (length != null))
				return new Position(start.intValue(), length.intValue());
		}
		return this.fTermPositionMap.get(term);
	}
	
	private void resetTermPositionMap(Spec spec, IDocument document) {
		Object[] children = spec.getChildren();
		int start = 0;
		int end = document.getLength() - 1;
		
		this.fTermPositionMap.clear();
		this.fTermPositionMap.putAll(
				getTermPositionMapFromChildren(
						children,
						document,
						start,
						end));
	}
	
	private Map<Term, Position> getTermPositionMapFromChildren(Object[] terms, IDocument document, int defaultStart, int defaultEnd) {
		Map<Term, Position> map = new HashMap<Term, Position>();
		
		int next = -1;
		int prevEnd = -1; // the offset of previous term's end
		int nextStart = -1; // the offset of next term's start
//		System.out.println("terms.length: " + terms.length);
		
		for(int current = 0; current < terms.length;) {
			next = current + 1;
//			System.out.println("next: " + next);
//			if (terms[current] != null)
//				System.out.println("current.class: " + current + ". "+ terms[current].getClass().toString());
			if (terms[current] == null) {
			}
			else if (terms[current] instanceof Term) {
				// get the range directly
				Position range = getRangeOfTerm((Term)terms[current]);
				if (range != null) {
//					System.out.println("Position: (" + range.getOffset() + ", " + (range.getOffset() + range.getLength() - 1) + ")");
					map.put((Term)terms[current], range);
					nextStart = range.getOffset() + range.getLength();
					if (!(terms[current] instanceof ZRefName)) {
						map.putAll(getTermPositionMapFromChildren(
								((Term)terms[current]).getChildren(),
								document,
								range.getOffset(),
								range.getOffset() + range.getLength() - 1));
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
						start = getRangeStart((Term)terms[current], document);
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
				
					int length = getTermLength((Term)terms[current]);
					if (length > 0)
						end = start + length - 1;
					else {
						end = getChildrenEnd((Term)terms[current]);
						if (end < 0) {
							for (; next < terms.length; next++) {
//								System.out.println("next inside: " + next);
//								System.out.println("next inside class: " + terms[next].getClass());
								if (terms[next] instanceof Term) {
									nextStart = getRangeStart((Term)terms[next], document);
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
						map.put((Term)terms[current], new Position(start, end - start + 1));
						if (!(terms[current] instanceof ZRefName)) {
							map.putAll(getTermPositionMapFromChildren(
									((Term)terms[current]).getChildren(),
									document,
									start,
									end));
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
	private Position getRangeOfTerm(Term term) {
		LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
		
		if (locAnn != null) {
			BigInteger rangeStart = locAnn.getStart();
			BigInteger rangeLength = locAnn.getLength();
			if ((rangeStart != null) || (rangeLength != null))
				return new Position(rangeStart.intValue(), rangeLength.intValue());
		}
		
		return null;
	}
	
	private int getRangeStart(Term term, IDocument document) {
//		System.out.println("term.class: " + term.getClass());
		LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
		
		if (locAnn != null) {
			BigInteger start = locAnn.getStart();
			if (start != null) {
//				System.out.println("locAnn.getStart: " + start);
				return start.intValue();
			}
			
			try {
				int line = locAnn.getLine().intValue();
				int column = locAnn.getCol().intValue();
				
//				System.out.println("line: " + line);
//				System.out.println("column: " + column);
//				System.out.println("lineoffset: " + document.getLineOffset(line));
				return document.getLineOffset(line) + column;
			} catch (BadLocationException ble) {
			}
		}
		else {
			Object[] objects = term.getChildren();
			int start = -1;
			for (int i = 0; i < objects.length; i++) {
				if (objects[i] instanceof Term)
					start = getRangeStart((Term)objects[i], document);
				if (start > -1)
					return start;
			}
		}

		return -1;
	}
	
	private int getTermLength(Term term) {
		LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
		
		if (locAnn != null) {
			BigInteger length = locAnn.getLength();
			if (length != null)
				return length.intValue();
		}
		
		return -1;
	}
	
	private int getChildrenEnd(Term term) {
//		System.out.println("term.class: " + term.getClass());
		Object[] children = term.getChildren();
		int end = -1;
		for (int i = children.length - 1; i >= 0; i--)
			if (children[i] instanceof Term) {
				LocAnn locAnn = (LocAnn) ((Term)children[i]).getAnn(LocAnn.class);
				if (locAnn != null) {
					BigInteger start = locAnn.getStart();
					BigInteger length = locAnn.getLength();
					if ((start != null) && (length != null)) {
//						System.out.println("locAnn.getStart: " + start);
						end = start.intValue() + length.intValue() - 1;
						if (end < 0)
							end = getChildrenEnd((Term)children[i]);
					}
				}
				else
					end = getChildrenEnd((Term)children[i]);
				
				if (end > -1)
					break;
			}
		
		return end;
	}
}
