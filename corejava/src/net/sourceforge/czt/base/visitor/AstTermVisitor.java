/**
Copyright 2003 Mark Utting
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.base.visitor;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.util.Visitor;
import java.util.*;

/**
 * A substitution visitor for visiting
 * {@link net.sourceforge.czt.base.ast.Term Z terms}.
 * This visitor visits recursively all children of a term.
 * The visitor returns either the object it is visiting, indicating that no
 * substitution has taken place, or a new term with the substitution applied.
 *
 * This class handles all Terms within the visitTerm(Term) method.
 * If an extending class provides, for instance, a visitExpr(Expr) method,
 * all Expr objects (including all objects derived from Expr) are handled
 * by this method instead of the visitTerm(Term) method.
 *
 * This class does not do any substitution, but derived classes can.
 *
 * @author Petra Malik
 */
public class AstTermVisitor implements TermVisitor, TermAVisitor
{
  /**
   * The class name of this class; used for logging purposes.
   */
  private static final String sClassName = "AstTermVisitor";

  /**
   * The methods of this class use this logger.
   */
  private static final java.util.logging.Logger sLogger =
    java.util.logging.Logger.getLogger("net.sourceforge.czt.base.util." +
				       sClassName);

  /**
   * Visits a list by visiting all the elements contained in this list.
   * @param list the list to be visited.
   * @return a list containing the return values of the visit-calls.
   *         Argument list is returned unchanged
   *         iff each visit call returns the object it is visiting.
   */
  public List visitList(List list) {
    sLogger.entering(sClassName, "visitList", list);
    boolean changed = false;
    List newList = new Vector(list.size());
    for(Iterator iter=list.iterator(); iter.hasNext();) {
      Object oldObject = iter.next();
      if (oldObject instanceof Term) {
	Object newObject = ((Term)oldObject).accept(this);
	if (newObject != null) newList.add(newObject);
	if (oldObject != newObject) { changed = true; }
      }
    }
    if (changed) {
      sLogger.fine("List has changed.");
      sLogger.exiting(sClassName, "visitList", newList);
      return newList;
    }
      sLogger.exiting(sClassName, "visitList", list);
    return list;
  }

  /**
   * Visits a term by visiting all its children.
   * @param term the term to be visited.
   * @return a term that has the return values of the visit calls as children.
   *         Argument term is returned unchanged
   *         iff each visit call returns the object it is visiting.
   */
  public Object visitTerm(Term term) {
    sLogger.entering(sClassName, "visitTerm", term);
    boolean changed = false;

    Object[] args = term.getChildren();
    for (int i=0; i < args.length; i++) {
      if (args[i] != null) {
	if (args[i] instanceof Term) {
	  Term t = (Term) ((Term)args[i]).accept(this);
	  if (t != args[i]) {
	    args[i] = t;
	    changed = true;
	  }
	} else if (args[i] instanceof List) {
	  List l = (List) visitList((List) args[i]);
	  if (l != args[i]) {
	    args[i] = l;
	    changed = true;
	  }
	}
      }
    }
    if (! changed) {
      sLogger.exiting(sClassName, "visitTerm", term);
      return term;
    }
    sLogger.fine("Term has changed.");
    Term erg = term;
    try {
      erg = term.create(args);
    } catch(Exception e) {
      sLogger.warning("The children of the Term " + term.toString() +
		      " object have been substituted by a type " +
		      "that is not acceptable as a valid child. " +
		      "No new Term is created.");
    }
    sLogger.exiting(sClassName, "visitTerm", erg);
    return erg;
  }

  /**
   * Visits an {@link TermA annotated term} by calling #visitTerm
   * and, in case the term has changed, setting the annotation
   * appropriately.
   */
  public Object visitTermA(TermA term)
  {
    final String methodName = "visitTermA";
    sLogger.entering(sClassName, methodName, term);
    Object result = visitTerm(term);
    if (term != result && result instanceof TermA) {
      sLogger.fine("Setting the annotations.");
      TermA newTerm = (TermA) result;
      newTerm.getAnns().addAll(term.getAnns());
    }
    sLogger.exiting(sClassName, methodName, result);
    return result;
  }
}
