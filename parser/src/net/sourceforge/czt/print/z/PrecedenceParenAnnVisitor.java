/*
Copyright (C) 2004 Petra Malik
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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.ast.TermA;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
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
  implements TermVisitor,
             PredVisitor, ExprVisitor, ProdExprVisitor,
             ApplicationVisitor, OperatorApplicationVisitor
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
   */
  public void run(Term term)
  {
    term.accept(this);
  }

  public Object visitTerm(Term term)
  {
    VisitorUtils.visitTerm(this, term);
    return null;
  }

  public Object visitPred(Pred term)
  {
    VisitorUtils.visitTerm(this, term);
    preservePrecedence(term);
    return null;
  }

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
          List list = (List) child;
          for (Iterator iter = list.iterator(); iter.hasNext();) {
            Object elem = iter.next();
            addParenAnnIfNecessary(elem, prec);
          }
        }
        else if (child instanceof TermA) {
          addParenAnnIfNecessary((TermA) child, prec);
        }
      }
    }
  }

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
    return OperatorName.Fixity.INFIX.equals(opName.getFixity());
  }

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

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    VisitorUtils.visitTerm(this, prodExpr);
    preservePrecedence(prodExpr);
    for (Iterator iter = prodExpr.getExpr().iterator(); iter.hasNext(); ) {
      Object child = iter.next();
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
    if (object instanceof TermA) {
      addParenAnnIfNecessary((TermA) object, parentPrec);
    }
  }

  /**
   * Adds parenthesis annotations to the given term
   * if the precedence of the parent is greater than
   * the precedence of the given term.
   *
   * @param termA the term to which annotations are added, if necessary.
   * @param parentPrec the precedence of the parent.
   */
  protected void addParenAnnIfNecessary(TermA termA, Precedence parentPrec)
  {
    Precedence prec = precedence(termA);
    if (prec != null && parentPrec.compareTo(prec) > 0) {
      addParenAnn(termA);
    }
  }

  protected void addParenAnn(TermA termA)
  {
    termA.getAnns().add(factory_.createParenAnn());
  }

  protected boolean isConjunctionPred(Term term)
  {
    if (term instanceof AndPred) {
      AndPred andPred = (AndPred) term;
      Op op = andPred.getOp();
      return op.equals(Op.And) || op.equals(Op.Chain);
    }
    return false;
  }

  protected boolean newLineOrSemicolonConj(Term term)
  {
    if (term instanceof AndPred) {
      AndPred andPred = (AndPred) term;
      Op op = andPred.getOp();
      return op.equals(Op.NL) || op.equals(Op.Semi);
    }
    return false;
  }

  public Precedence precedence(Term t)
  {
    if      (t instanceof ThetaExpr)         return new Precedence(250);

    else if (t instanceof BindSelExpr ||
             t instanceof TupleSelExpr)      return new Precedence(240);

    else if (t instanceof RenameExpr)        return new Precedence(230);

    else if (t instanceof DecorExpr)         return new Precedence(220);

    else if (t instanceof Application)       return new Precedence(210);
    else if (t instanceof OperatorApplication) {
      OperatorApplication appl = (OperatorApplication) t;
                                             return appl.getPrecedence();
    }
    else if (t instanceof PowerExpr)         return new Precedence(190);

    else if (t instanceof ProdExpr)          return new Precedence(180, 8);

    else if (t instanceof PreExpr)           return new Precedence(170);

    else if (t instanceof ProjExpr)          return new Precedence(160);

    else if (t instanceof HideExpr)          return new Precedence(150);

    else if (t instanceof PipeExpr)          return new Precedence(140);

    else if (t instanceof CompExpr)          return new Precedence(130);

    else if (t instanceof CondExpr)          return new Precedence(120);

    else if (t instanceof LetExpr)           return new Precedence(110);

    else if (t instanceof MuExpr)            return new Precedence(100);

    else if (t instanceof LambdaExpr)        return new Precedence( 90);

    else if (t instanceof MemPred)           return new Precedence( 80);

    else if (t instanceof NegPred ||
             t instanceof NegExpr)           return new Precedence( 70);

    else if (isConjunctionPred(t) ||
             t instanceof AndExpr)           return new Precedence( 60);

    else if (t instanceof OrPred ||
             t instanceof OrExpr)            return new Precedence( 50);

    else if (t instanceof ImpliesPred ||
             t instanceof ImpliesExpr)       return new Precedence( 40);

    else if (t instanceof IffPred ||
             t instanceof IffExpr)           return new Precedence( 30);

    else if (t instanceof ForallPred ||
             t instanceof ExistsPred ||
             t instanceof Exists1Pred ||
             t instanceof ForallExpr ||
             t instanceof ExistsExpr ||
             t instanceof Exists1Expr)       return new Precedence( 20);

    else if (newLineOrSemicolonConj(t))      return new Precedence( 10);
    return null;
  }
}
