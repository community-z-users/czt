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
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.visitor.*;

/**
 * This visitor visits an AST and annotates each terms with a parenthesis
 * annotation that has a child of higher priority.
 * The parenthesis are needed when this AST is printed.
 */
public class PrecedenceParenAnnVisitor
  implements TermVisitor, ZSectVisitor,
             PredVisitor, ExprVisitor, ProdExprVisitor,
             ApplicationVisitor, OperatorApplicationVisitor
{
  private Factory factory_ = new Factory();
  private OpTable opTable_;
  private SectionManager manager_;

  public PrecedenceParenAnnVisitor(SectionManager manager)
  {
    manager_ = manager;
  }

  public void reset()
  {
    opTable_ = null;
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
    double prec = precedence(term);
    if (prec >= 0) {
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

  public Object visitOperatorApplication(OperatorApplication appl)
  {
    VisitorUtils.visitTerm(this, appl);
    preservePrecedence(appl);
    OperatorName opName = appl.getOperatorName();
    if (isInfix(opName)) {
      Assoc assoc = null;
      if (opTable_ != null) {
        OpTable.OpInfo opInfo = opTable_.lookup(opName);
        if (opInfo != null) {
          assoc = opInfo.getAssoc();
        }
      }
      else {
        String message = "Cannot get associativity for '" + opName +
          "'; no operator table available.";
        CztLogger.getLogger(PrecedenceParenAnnVisitor.class).warning(message);
      }
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

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    opTable_ = manager_.getOperatorTable(name);
    if (opTable_ == null) {
      List parentOpTables = new ArrayList();
      for (Iterator iter = zSect.getParent().iterator(); iter.hasNext(); ) {
        Parent parent = (Parent) iter.next();
        OpTable parentOpTable = manager_.getOperatorTable(parent.getWord());
        if (parentOpTable != null) {
          parentOpTables.add(parentOpTable);
        }
      }
      if (parentOpTables.size() > 0) {
        try {
          opTable_ = new OpTable(zSect.getName(), parentOpTables);
        }
        catch (OpTable.OperatorException e) {
          CztLogger.getLogger(PrecedenceParenAnnVisitor.class).warning(e.getMessage());
        }
      }
    }
    return visitTerm(zSect);
  }

  /**
   * Adds parenthesis annotations to the given object
   * if it is an annotable term and
   * the precedence of the parent is greater than
   * the precedence of the given term.
   *
   * @param termA the term to which annotations are added, if necesasry.
   * @param parentPrecedence the precedence of the parent.
   */
  protected void addParenAnnIfNecessary(Object object, double parentPrec)
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
  protected void addParenAnnIfNecessary(TermA termA, double parentPrec)
  {
    double prec = precedence(termA);
    if (prec != -1 && parentPrec > prec) {
      addParenAnn(termA);
    }
  }

  protected void addParenAnn(TermA termA)
  {
    termA.getAnns().add(factory_.createParenAnn());
  }

  /**
   * Returns the operator name if the given term is a function
   * or generic operator application, <code>null</code> otherwise.
   */
  protected static OperatorName isFunOrGenOpAppl(Term term)
  {
    if (term instanceof ApplExpr) {
      // function operator application
      ApplExpr applExpr = (ApplExpr) term;
      if (applExpr.getMixfix().booleanValue()) {
        Expr leftExpr = applExpr.getLeftExpr();
        if (leftExpr instanceof RefExpr) {
          return ((RefExpr) leftExpr).getRefName().getOperatorName();
        }
      }
    }
    else if (term instanceof OperatorApplication)
    {
      OperatorApplication opApp = (OperatorApplication) term;
      return opApp.getOperatorName();
    }
    else if (term instanceof RefExpr) {
      // generic operator application
      RefExpr refExpr = (RefExpr) term;
      if (refExpr.getMixfix().booleanValue() &&
          refExpr.getExpr().size() > 0) {
        return refExpr.getRefName().getOperatorName();
      }
    }
    return null;
  }

  protected boolean isPostfix(OperatorName opName)
  {
    if (opName == null) return false;
    return OperatorName.Fixity.POSTFIX.equals(opName.getFixity());
  }

  protected boolean isPrefix(OperatorName opName)
  {
    if (opName == null) return false;
    return OperatorName.Fixity.PREFIX.equals(opName.getFixity());
  }

  protected boolean isInfix(OperatorName opName)
  {
    if (opName == null) return false;
    return OperatorName.Fixity.INFIX.equals(opName.getFixity());
  }

  protected boolean isNofix(OperatorName opName)
  {
    if (opName == null) return false;
    return OperatorName.Fixity.NOFIX.equals(opName.getFixity());
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

  public double precedence(Term t)
  {
    OperatorName opName = null;
    if      (t instanceof ThetaExpr)         return 250;

    else if (t instanceof BindSelExpr ||
             t instanceof TupleSelExpr)      return 240;

    else if (t instanceof RenameExpr)        return 230;

    else if (t instanceof DecorExpr)         return 220;

    else if (t instanceof Application)       return 210;

    else if (isPostfix(isFunOrGenOpAppl(t))) return 200;

    else if (t instanceof PowerExpr ||
             isPrefix(isFunOrGenOpAppl(t)))  return 190;

    else if ((opName = isFunOrGenOpAppl(t)) != null &&
             isInfix(opName)) {
      if (opTable_ != null) {
        OpTable.OpInfo opInfo = opTable_.lookup(opName);
        if (opInfo != null && opInfo.getPrec() != null) {
          double prec = opInfo.getPrec().intValue();
          prec = prec / 1000000;
                                             return 180 + prec;
        }
      }
      else {
        String message = "Cannot get precedence for '" + opName +
          "'; no operator table available.";
        CztLogger.getLogger(PrecedenceParenAnnVisitor.class).warning(message);
      }
                                             return 180;
    }
    else if (t instanceof ProdExpr)          return 180 + 8.0/1000000;

    else if (t instanceof PreExpr)           return 170;

    else if (t instanceof ProjExpr)          return 160;

    else if (t instanceof HideExpr)          return 150;

    else if (t instanceof PipeExpr)          return 140;

    else if (t instanceof CompExpr)          return 130;

    else if (t instanceof CondExpr)          return 120;

    else if (t instanceof LetExpr)           return 110;

    else if (t instanceof MuExpr)            return 100;

    else if (t instanceof LambdaExpr)        return  90;

    else if (t instanceof MemPred)           return  80;

    else if (t instanceof NegPred ||
             t instanceof NegExpr)           return  70;

    else if (isConjunctionPred(t) ||
             t instanceof AndExpr)           return  60;

    else if (t instanceof OrPred ||
             t instanceof OrExpr)            return  50;

    else if (t instanceof ImpliesPred ||
             t instanceof ImpliesExpr)       return  40;

    else if (t instanceof IffPred ||
             t instanceof IffExpr)           return  30;

    else if (t instanceof ForallPred ||
             t instanceof ExistsPred ||
             t instanceof Exists1Pred ||
             t instanceof ForallExpr ||
             t instanceof ExistsExpr ||
             t instanceof Exists1Expr)       return  20;

    else if (newLineOrSemicolonConj(t))      return  10;
    return -1;
  }
}
