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

package net.sourceforge.czt.zpatt.util;

import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * @author Petra Malik
 */
public class Substitution
{
  private Map bindings_ = new HashMap();

  private SubstList substList_;

  public Substitution()
  {
  }

  public Substitution(SubstList substList)
  {
    substList_ = substList;
  }

  /**
   * Provide a warning message.
   */
  private void logWarning(String message)
  {
    final String name = "net.sourceforge.czt.core.util.Substitution";
    Logger.getLogger(name).warning(message);
  }

  public Term substitute(Term t)
  {
    if (substList_ != null) {
      Blubb blubb = new Blubb();
      return (Term) t.accept(blubb);
    }
    return null;
  }

  public Map getBindings()
  {
    return bindings_;
  }

  /**
   * Binds the jokers from the last match run.
   */
  public Term bind(Term term)
  {
    JokerSubstVisitor v = new JokerSubstVisitor();
    return (Term) term.accept(v);
  }

  /**
   * Matches a term which may contain joker agains a term
   * without joker.
   *
   * @param term1 a term that may contain joker.
   * @param term2 a term without joker.
   * @return a list of bindings,
   *         or <code>null</code> if the two terms do not match.
   */
  public boolean match(Term term1, Term term2)
  {
    if (term1 == term2) return true;
    if (term1 instanceof JokerExpr) {
      if (term2 instanceof Expr) {
	JokerExpr joker = (JokerExpr) term1;
	String name = joker.getName();
	if (name != null) {
	  Term t = (Term) bindings_.get(name);
	  if (t != null) {
	    return t.equals(term2);
	  }
	  bindings_.put(name, term2);
	}
	return true;
      } else {
	// term2 has wrong type
	return false;
      }
    }
    if (term1 instanceof JokerPred) {
      if (term2 instanceof Pred) {
	JokerPred joker = (JokerPred) term1;
	String name = joker.getName();
	if (name != null) {
	  Term t = (Term) bindings_.get(name);
	  if (t != null) {
	    return t.equals(term2);
	  }
	  bindings_.put(name, term2);
	}
	return true;
      } else {
	// term2 has wrong type
	return false;
      }
    }
    if (term1.getClass() != term2.getClass()) return false;
    Object[] args1 = term1.getChildren();
    Object[] args2 = term2.getChildren();
    for (int i=0; i < args1.length; i++) {
      if (args1[i] == null && args2[i] != null) { return false; }
      if (args1[i] != null) {
	if (args1[i] instanceof Term) {
	  Term child1 = (Term) args1[i];
	  Term child2 = (Term) args2[i];
	  if (!match(child1, child2)) return false;
	} else if (args1[i] instanceof List) {
	  List list1 = (List) args1[i];
	  List list2 = (List) args2[i];
	  if (!match(list1, list2)) return false;
	} else {
	  if (! args1[i].equals(args2[i])) return false;
	}
      }
    }
    return true;
  }

  private boolean match(List list1, List list2)
  {
    if(list1.size() != list2.size()) return false;
    for(int i=0; i < list1.size(); i++) {
      Object o1 = list1.get(i);
      Object o2 = list2.get(i);
      if (o1 instanceof Term && o2 instanceof Term) {
	if (!match((Term) o1, (Term) o2)) return false;
      } else {
	if (! o1.equals(o2)) return false;
      }
    }
    return true;
  }

  class Blubb
    implements TermVisitor, TermAVisitor, ExprVisitor, PredVisitor
  {
    /**
     * Visit all children of a term.
     */
    public Object visitTerm(Term term)
    {
      return VisitorUtils.visitTerm(this, term, true);
    }
    
    /**
     * Visit all children of a term and copy annotations.
     */
    public Object visitTermA(TermA oldTermA)
    {
      TermA newTermA = (TermA)visitTerm(oldTermA);
      if (newTermA != oldTermA) {
	newTermA.getAnns().addAll(oldTermA.getAnns());
      }
      return newTermA;
    }
    
    public Object visitExpr(Expr expr)
    {
      return visit(expr);
    }

    public Object visitPred(Pred pred)
    {
      return visit(pred);
    }

    private Object visit(Term t) {
      for (Iterator iter = substList_.getSubstitute().iterator();
	   iter.hasNext();)
      {
	Substitute subst = (Substitute) iter.next();
	Term t1 = null;
	Term t2 = null;
	if (! subst.getExpr().isEmpty()) {
	  t1 = (Term) subst.getExpr().get(0);
	  t2 = (Term) subst.getExpr().get(1);
	}
	if (! subst.getPred().isEmpty()) {
	  t1 = (Term) subst.getPred().get(0);
	  t2 = (Term) subst.getPred().get(1);
	}
	bindings_.clear();
	if (match(t1, t)) {
	  return bind(t2);
	}
      }
      return t;
    }
  }

  class JokerSubstVisitor
    implements TermVisitor, TermAVisitor, ZpattVisitor {

    /**
     * Visit all children of a term.
     */
    public Object visitTerm(Term term)
    {
      return VisitorUtils.visitTerm(this, term, true);
    }
    
    /**
     * Visit all children of a term and copy annotations.
     */
    public Object visitTermA(TermA oldTermA)
    {
      TermA newTermA = (TermA)visitTerm(oldTermA);
      if (newTermA != oldTermA) {
	newTermA.getAnns().addAll(oldTermA.getAnns());
      }
      return newTermA;
    }
    
    /**
     * Visits a(n) JokerExpr.
     * @param  joker the JokerExpr to be visited.
     * @return some kind of <code>Object</code>.
     */
    public Object visitJokerExpr(JokerExpr joker)
    {
      Expr newExpr = (Expr) bindings_.get(joker.getName());
      if (newExpr != null) return newExpr;
      logWarning("Could not find binding for JokerExpr " + joker.getName());
      return joker;
    }
    
    /**
     * Visits a(n) JokerPred.
     * @param  joker the JokerPred to be visited.
     * @return some kind of <code>Object</code>.
     */
    public Object visitJokerPred(JokerPred joker)
    {
      Pred newPred = (Pred) bindings_.get(joker.getName());
      if (newPred != null) return newPred;
      logWarning("Could not find binding for JokerPred " + joker.getName());
      return joker;
    }
    
    /**
     * Visits a(n) Substitute.
     * @param  zedObject the Substitute to be visited.
     * @return some kind of <code>Object</code>.
     */
    public Object visitSubstitute(Substitute zedObject)
    {
      throw new UnsupportedOperationException();
    }
    
    /**
     * Visits a(n) SubstList.
     * @param  zedObject the SubstList to be visited.
     * @return some kind of <code>Object</code>.
     */
    public Object visitSubstList(SubstList zedObject)
    {
      throw new UnsupportedOperationException();
    }
  }
}
