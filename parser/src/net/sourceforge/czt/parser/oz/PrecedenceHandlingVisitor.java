package net.sourceforge.czt.parser.oz;

import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.StringTokenizer;

import java_cup.runtime.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.util.CztException;

/**
 * A <code>PrecedenceHandler</code> re-arranges nested
 * <code>ApplExpr</code> invokations to
 */
public class PrecedenceHandlingVisitor
  implements TermVisitor,
	     ZSectVisitor,
	     ParentVisitor,
	     ApplExprVisitor
{
  /** The token for an argument in an operator name */
  public final static String ARG_TOK = "_";

  /** The operator table used to determine the precedence of operators */
  protected OperatorTable table_;

  /** A <code>ZFactory</code> */
  protected ZFactory zFactory_ = new ZFactoryImpl();

  /**
   * Construct an instance of this handler with a specified
   * operator table
   */
  public PrecedenceHandlingVisitor(OperatorTable table)
  {
    table_ = table;
  }

  /**
   * Visits all of its children
   */
  public Object visitTerm(Term term)
  {
    Object [] children = term.getChildren();

    for (int i = 0; i < children.length; i++) {
      Object child = children[i];

      //call this method recursively on each child
      if (child instanceof Term) {
	((Term) child).accept(this);
      }
      else if (child instanceof List) {
	List list = (List) child;
	for (Iterator iter = list.iterator(); iter.hasNext(); ) {
	  Object next = iter.next();

	  if (next instanceof Term) {
	    ((Term) next).accept(this);
	  }
	}
      }
    }
    return null;
  }

  /**
   * We must visit a ZSect in order to set the current section in the
   * operator table
   */
  public Object visitZSect(ZSect zSect)
  {
    String name = zSect.getName();
    table_.setSection(name);

    //get and visit each parent
    List parent = zSect.getParent();
    for (Iterator iter = parent.iterator(); iter.hasNext(); ) {
      Parent next = (Parent) iter.next();
      next.accept(this);
    }

    //get and visit each paragraph
    List para = zSect.getPara();
    for (Iterator iter = para.iterator(); iter.hasNext(); ) {
      Para next = (Para) iter.next();
      next.accept(this);
    }    
    return null;
  }

  /**
   * We must visit a ZSect in order to set the parents in the operator
   * table
   */
  public Object visitParent(Parent parent)
  {
    String name = parent.getWord();
    table_.addParent(name);
    return null;
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
    //first visit the children of this ApplExpr
    Expr leftExpr = applExpr.getLeftExpr();
    Expr rightExpr = applExpr.getRightExpr();

    if (leftExpr != null) {
      leftExpr.accept(this);
    }

    if (rightExpr != null) {
      rightExpr.accept(this);
    }

    //if we need to reorder this ApplExpr with its left sub-child
    if (needsReordering(applExpr)) {

      //due to java's reference semantics, the values inside the objects
      //must be swapped, rather than the references themselves

      //we know that the first element of the tuple is another ApplExpr,
      //so this should always be safe
      List parentTuple = ((TupleExpr) leftExpr).getExpr();
      ApplExpr child = (ApplExpr) parentTuple.get(0);

      //swap the names
      RefExpr parentName = (RefExpr) rightExpr;
      RefExpr childName = (RefExpr) child.getRightExpr();
      RefName swapName =
	zFactory_.createRefName(parentName.getRefName().getWord(),
				parentName.getRefName().getStroke(),
				parentName.getRefName().getDecl());
      parentName.setRefName(childName.getRefName());
      childName.setRefName(swapName);

      //remove all but the first element of the parent tuple
      List fromParentTuple = 
	new ArrayList(parentTuple.subList(1, parentTuple.size()));
      parentTuple.removeAll(fromParentTuple);

      //move all but the last argument of the child to the front
      //of the parents tuple
      List childTuple = ((TupleExpr) child.getLeftExpr()).getExpr();
      List fromChildTuple = 
	new ArrayList(childTuple.subList(0, childTuple.size() - 1));
      childTuple.removeAll(fromChildTuple);
      parentTuple.addAll(0, fromChildTuple);

      //move everything after the ApplExpr in the parent's tuple to 
      //the end of the child's tuple
      childTuple.addAll(fromParentTuple);
    }

    return null;
  }

  /**
   * Returns true if an only if a specified <code>ApplExpr</code> has
   * a nested <code>ApplExpr</code> without parenthesise (no
   * <code>ParenAnn</code> annotation) that has a lower precedence
   * then it
   */
  protected boolean needsReordering(ApplExpr applExpr)
  {
    Expr leftExpr = applExpr.getLeftExpr();

    //if the left expression is not a TupleExpr, then
    //we do not have a nested ApplExpr
    if (!(leftExpr instanceof TupleExpr)) {
      return false;
    }

    //if the TupleExpr does not have an ApplExpr in its
    //first position, then we do not have a nested ApplExpr
    TupleExpr tupleExpr = (TupleExpr) leftExpr;    
    List tuple = tupleExpr.getExpr();
    if (tuple.size() < 2 || !(tuple.get(0) instanceof ApplExpr)) {
      return false;
    }

    //if the nested ApplExpr has parenthesise, or the nested
    //expression is not mixfix, then no reordering is required
    ApplExpr nestedApplExpr = (ApplExpr) tuple.get(0);    
    if (hasParenAnn(nestedApplExpr) ||
	nestedApplExpr.getMixfix().equals(Boolean.FALSE)) {
      return false;
    }

    //get the precedences of the two expressions
    int prec = getPrec(applExpr);
    int nestedPrec = getPrec(nestedApplExpr);

    //if the precedence of applExpr is lower than the precedence of
    //nestedApplExpr, or they are not infix operators (no precedence
    //info) then no reordering is required
    if (prec < nestedPrec || prec == 0 || nestedPrec == 0) {
      return false;
    }

    //get the associativities of the two expressions
    Assoc assoc = getAssoc(applExpr);
    Assoc nestedAssoc = getAssoc(nestedApplExpr);

    //if the precedences are the same, but the associativity of
    //applExpr is Left, then no reordering is required
    if (prec == nestedPrec && assoc == Assoc.Left) {
      return false;
    }

    //if we get to here, then reordering is required
    return true;
  }

  //returns true if and only if the specified TermA has a
  //ParenAnn in its annotations
  private boolean hasParenAnn(TermA termA)
  {
    //get the list of annotations
    List anns = termA.getAnns();

    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      //if the next annotation is a ParenAnn
      if (iter.next() instanceof ParenAnn) {
	return true;
      }
    }
    return false;
  }

  //returns the precedence of the name in an ApplExpr
  //precondition: the right expr is a RefExpr
  private int getPrec(ApplExpr applExpr)
  {
    String first = getFirstInfixName(applExpr);

    int prec = 0;
    if (first != null) {
      prec = table_.getPrec(first);
    }
    return prec;
  }

  //returns the associativity of the name in an ApplExpr
  //precondition: the right expr is a RefExpr
  private Assoc getAssoc(ApplExpr applExpr)
  {
    String first = getFirstInfixName(applExpr);

    Assoc assoc = null;;
    if (first != null) {
      assoc = table_.getAssoc(first);
    }
    return assoc;
  }

  private String getName(ApplExpr applExpr)
  {  
    if (applExpr.getRightExpr() instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) applExpr.getRightExpr();
      String name = refExpr.getRefName().getWord();
      return name;
    }
    return "Unknown";
  }

  private String getFirstInfixName(ApplExpr applExpr)
  {
    String result = null;
    String name = getName(applExpr);

    //if the first token is not "_", return null
    StringTokenizer st = new StringTokenizer(name);
    if (st.hasMoreTokens()) {
      String first = st.nextToken();
      if (!first.equals(ARG_TOK)) {
	result = null;
      }
      else {
	if (st.hasMoreTokens()) {
	  //if the second token is a "_", return null
	  String second = st.nextToken();
	  if (second.equals(ARG_TOK)) {
	    result = null;
	  }
	  else {
	    result = second;
	  }
	}
      }
    }
    else {
      result = null;
    }
    return result;
  }
}
