/*
  Copyright (C) 2004, 2006 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.Fixity;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.visitor.*;

/**
 * This visitor visits an printable AST and adds necessary parentheses.
 *
 * <p>The input tree must be a tree created by the AstToPrintTreeVisitor.
 * This visitor adds parenthesis annotations to terms where parenthesis
 * are needed to preserve the syntactical structure of the operators
 * when printed.  That is, parenthesis annotations are added when a
 * term does not already has one, and either the parent term has a
 * higher priority, or the parent has the same priority but the
 * parenthesis is enforced by associativity.</p>
 *
 * <p>For instance, a conjunction where one of the arguments is an
 * implication needs parenthesis around the implication, since
 * conjunction has higher priority than implication.  For the second
 * example, recall that implication is right associative.  An
 * implication that has an implication as its first (left) argument
 * needs parenthesis around, whereas an implication as second (right)
 * argument does not need parenthesis.</p>
 *
 * @author Petra Malik
 */
public class PrecedenceParenAnnVisitor
  implements TermVisitor<Object>,
             PredVisitor<Object>,
             ExprVisitor<Object>,
             ProdExprVisitor<Object>,
             ApplicationVisitor<Object>,
             OperatorApplicationVisitor<Object>
{
  /**
   * A factory used to create the parenthesis annotations.
   */
  private Factory factory_ = new Factory();

  /**
   * <p>Visits a term and its children
   * and adds ParenAnn to terms where this is
   * needed to enforce the given precedence and
   * associativity.</p>
   * @param term
   */
  public void run(Term term)
  {
    term.accept(this);
  }

  @Override
  public Object visitTerm(Term term)
  {
    VisitorUtils.visitTerm(this, term);
    return null;
  }

  @Override
  public Object visitPred(Pred term)
  {
    VisitorUtils.visitTerm(this, term);
    preservePrecedence(term);
    return null;
  }

  @Override
  public Object visitExpr(Expr term)
  {
    VisitorUtils.visitTerm(this, term);
    preservePrecedence(term);
    return null;
  }

  protected void preservePrecedence(Term term)
  {
    Precedence prec = precedence(term);
    if (prec != null) {
      Object[] children = term.getChildren();
      for (int i = 0; i < children.length; i++) {
        Object child = children[i];
        if (child instanceof List) {
          @SuppressWarnings("unchecked")
		List<Object> list = (List<Object>) child;
          for (Iterator<Object> iter = list.iterator(); iter.hasNext();) {
            Object elem = iter.next();
            addParenAnnIfNecessary(elem, prec);
          }
        }
        else if (child instanceof Term) {
          addParenAnnIfNecessary((Term) child, prec);
        }
      }
    }
  }

  @Override
  public Object visitApplication(Application appl)
  {
    VisitorUtils.visitTerm(this, appl);
    preservePrecedence(appl);
    Expr rightExpr = appl.getRightExpr();
    if (rightExpr instanceof Application) {
      addParenAnn(rightExpr);
    }
    return null;
  }

  protected boolean isInfix(OperatorName opName)
  {
    if (opName == null) return false;
    return Fixity.INFIX.equals(opName.getFixity());
  }

  @Override
  public Object visitOperatorApplication(OperatorApplication appl)
  {
    VisitorUtils.visitTerm(this, appl);
    preservePrecedence(appl);
    OperatorName opName = appl.getOperatorName();
    if (isInfix(opName)) {
      Assoc assoc = appl.getAssoc();
      if (assoc == null) {
        String message = "Cannot find associativity for '" + opName
          + "'; assume leftassoc";
        CztLogger.getLogger(PrecedenceParenAnnVisitor.class).warning(message);
        assoc = Assoc.Left;
      }
      if (Assoc.Right.equals(assoc)) {
        Object firstArg = appl.getArgs().get(0);
        if (firstArg instanceof OperatorApplication) {
          OperatorApplication childApp = (OperatorApplication) firstArg;
          if (isInfix(childApp.getOperatorName())) {
            addParenAnn(childApp);
          }
        }
      }
      else {
        Object lastArg = appl.getArgs().get(appl.getArgs().size() - 1);
        if (lastArg instanceof OperatorApplication) {
          OperatorApplication childApp = (OperatorApplication) lastArg;
          if (isInfix(childApp.getOperatorName())) {
            addParenAnn(childApp);
          }
        }
      }
    }
    return null;
  }

  @Override
  public Object visitProdExpr(ProdExpr prodExpr)
  {
    VisitorUtils.visitTerm(this, prodExpr);
    preservePrecedence(prodExpr);
    for (Iterator<Expr> iter = prodExpr.getZExprList().iterator();
         iter.hasNext(); ) {
      Expr child = iter.next();
      if (child instanceof ProdExpr) {
        addParenAnn((ProdExpr) child);
      }
    }
    return null;
  }

  /**
   * Adds parenthesis annotations to the given object
   * if it is an annotable term and
   * the precedence of the parent is greater than
   * the precedence of the given term.
   *
   * @param object the term to which annotations are added, if necesasry.
   * @param parentPrec the precedence of the parent.
   */
  protected void addParenAnnIfNecessary(Object object, Precedence parentPrec)
  {
    if (object instanceof Term) {
      addParenAnnIfNecessary((Term) object, parentPrec);
    }
  }

  /**
   * Adds parenthesis annotations to the given term
   * if the precedence of the parent is greater than
   * the precedence of the given term.
   *
   * @param term the term to which annotations are added, if necessary.
   * @param parentPrec the precedence of the parent.
   */
  protected void addParenAnnIfNecessary(Term term, Precedence parentPrec)
  {
    Precedence prec = precedence(term);
    if (prec != null && parentPrec.compareTo(prec) > 0) {
      addParenAnn(term);
    }
  }

  protected void addParenAnn(Term term)
  {
    term.getAnns().add(factory_.createParenAnn());
  }

  public Precedence precedence(Term term)
  {
    return term.accept(new PrecedenceVisitor());
  }
}
