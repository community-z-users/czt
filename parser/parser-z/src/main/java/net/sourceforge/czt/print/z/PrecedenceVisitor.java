/*
  Copyright (C) 2006, 2007 Petra Malik
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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.visitor.*;

/**
 * Throws NullPointerException if no operator table is given but a term
 * that needs a lookup in the operator table.
 *
 * @author Petra Malik
 */
public class PrecedenceVisitor
  implements TermVisitor<Precedence>,
             PrintPredicateVisitor<Precedence>,
             ThetaExprVisitor<Precedence>,
             BindSelExprVisitor<Precedence>,
             TupleSelExprVisitor<Precedence>,
             RenameExprVisitor<Precedence>,
             DecorExprVisitor<Precedence>,
             ApplExprVisitor<Precedence>,
             RefExprVisitor<Precedence>,
             ApplicationVisitor<Precedence>,
             OperatorApplicationVisitor<Precedence>,
             PowerExprVisitor<Precedence>,
             ProdExprVisitor<Precedence>,
             PreExprVisitor<Precedence>,
             ProjExprVisitor<Precedence>,
             HideExprVisitor<Precedence>,
             PipeExprVisitor<Precedence>,
             CompExprVisitor<Precedence>,
             CondExprVisitor<Precedence>,
             LetExprVisitor<Precedence>,
             MuExprVisitor<Precedence>,
             LambdaExprVisitor<Precedence>,
             MemPredVisitor<Precedence>,
             NegPredVisitor<Precedence>,
             NegExprVisitor<Precedence>,
             AndExprVisitor<Precedence>,
             AndPredVisitor<Precedence>,
             OrPredVisitor<Precedence>,
             OrExprVisitor<Precedence>,
             ImpliesPredVisitor<Precedence>,
             ImpliesExprVisitor<Precedence>,
             IffPredVisitor<Precedence>,
             IffExprVisitor<Precedence>,
             ForallPredVisitor<Precedence>,
             ExistsPredVisitor<Precedence>,
             Exists1PredVisitor<Precedence>,
             ForallExprVisitor<Precedence>,
             ExistsExprVisitor<Precedence>,
             Exists1ExprVisitor<Precedence>
{
  private OpTable opTable_;

  public PrecedenceVisitor()
  {
  }

  public PrecedenceVisitor(OpTable opTable)
  {
    opTable_ = opTable;
  }

  public Precedence visitTerm(Term term)
  {
    return null;
  }

  public Precedence visitPrintPredicate(PrintPredicate term)
  {
    return term.getPrecedence();
  }

  public Precedence visitThetaExpr(ThetaExpr term)
  {
    return Precedence.precedence(250);
  }

  public Precedence visitBindSelExpr(BindSelExpr term)
  {
    return Precedence.precedence(240);
  }

  public Precedence visitTupleSelExpr(TupleSelExpr term)
  {
    return Precedence.precedence(240);
  }

  public Precedence visitRenameExpr(RenameExpr term)
  {
    return Precedence.precedence(230);
  }

  public Precedence visitDecorExpr(DecorExpr term)
  {
    return Precedence.precedence(220);
  }

  public Precedence visitApplExpr(ApplExpr term)
  {
    final boolean isFunctionApplication =
      term.getMixfix().booleanValue();
    if (isFunctionApplication) {
      RefExpr refExpr = (RefExpr) term.getLeftExpr();
      OperatorName opName = refExpr.getZName().getOperatorName();
      return getPrecedence(opName);
    }
    return Precedence.precedence(210);
  }

  public Precedence visitRefExpr(RefExpr refExpr)
  {
    final boolean isGenericOperatorApplication =
      refExpr.getMixfix().booleanValue();
    if (isGenericOperatorApplication) {
      final OperatorName opName = refExpr.getZName().getOperatorName();
      return getPrecedence(opName);
    }
    return null;
  }

  public Precedence visitApplication(Application term)
  {
    return Precedence.precedence(210);
  }

  public Precedence visitOperatorApplication(OperatorApplication term)
  {
    return term.getPrecedence();
  }

  public Precedence visitPowerExpr(PowerExpr term)
  {
    return Precedence.precedence(190);
  }

  public Precedence visitProdExpr(ProdExpr term)
  {
    return Precedence.precedence(180, 8);
  }

  public Precedence visitPreExpr(PreExpr term)
  {
    return Precedence.precedence(170);
  }

  public Precedence visitProjExpr(ProjExpr term)
  {
    return Precedence.precedence(160);
  }

  public Precedence visitHideExpr(HideExpr term)
  {
    return Precedence.precedence(150);
  }

  public Precedence visitPipeExpr(PipeExpr term)
  {
    return Precedence.precedence(140);
  }

  public Precedence visitCompExpr(CompExpr term)
  {
    return Precedence.precedence(130);
  }

  public Precedence visitCondExpr(CondExpr term)
  {
    return Precedence.precedence(120);
  }

  public Precedence visitLetExpr(LetExpr term)
  {
    return Precedence.precedence(110);
  }

  public Precedence visitMuExpr(MuExpr term)
  {
    return Precedence.precedence(100);
  }

  public Precedence visitLambdaExpr(LambdaExpr term)
  {
    return Precedence.precedence(90);
  }

  public Precedence visitMemPred(MemPred memPred)
  {
    return Precedence.precedence(80);
  }

  public Precedence visitNegPred(NegPred term)
  {
    return Precedence.precedence(70);
  }

  public Precedence visitNegExpr(NegExpr term)
  {
    return Precedence.precedence(70);
  }

  public Precedence visitAndExpr(AndExpr term)
  {
    return Precedence.precedence(60);
  }

  public Precedence visitAndPred(AndPred term)
  {
    final And andType = term.getAnd();
    if (And.NL.equals(andType) || And.Semi.equals(andType)) {
      return Precedence.precedence(10);
    }
    return Precedence.precedence(60);
  }

  public Precedence visitOrPred(OrPred term)
  {
    return Precedence.precedence(50);
  }

  public Precedence visitOrExpr(OrExpr term)
  {
    return Precedence.precedence(50);
  }

  public Precedence visitImpliesPred(ImpliesPred term)
  {
    return Precedence.precedence(40);
  }

  public Precedence visitImpliesExpr(ImpliesExpr term)
  {
    return Precedence.precedence(40);
  }

  public Precedence visitIffPred(IffPred term)
  {
    return Precedence.precedence(30);
  }

  public Precedence visitIffExpr(IffExpr term)
  {
    return Precedence.precedence(30);
  }

  public Precedence visitForallPred(ForallPred term)
  {
    return Precedence.precedence(20);
  }

  public Precedence visitExistsPred(ExistsPred term)
  {
    return Precedence.precedence(20);
  }

  public Precedence visitExists1Pred(Exists1Pred term)
  {
    return Precedence.precedence(20);
  }

  public Precedence visitForallExpr(ForallExpr term)
  {
    return Precedence.precedence(20);
  }

  public Precedence visitExistsExpr(ExistsExpr term)
  {
    return Precedence.precedence(20);
  }

  public Precedence visitExists1Expr(Exists1Expr term)
  {
    return Precedence.precedence(20);
  }

  protected Precedence getPrecedence(OperatorName opName)
  {
    if (opName == null) return null;
    if (opName.isInfix()) {
      OpTable.OpInfo opInfo = opTable_.lookup(opName);
      if (opInfo != null) {
        if (opInfo.getPrec() == null) {
          String message =
            "Cannot find precedence of infix operator '" + opName + "'.";
          reportError(message);
        }
        final int prec = 180;
        return Precedence.precedence(prec, opInfo.getPrec().intValue());
      }
      else {
        String message =
          "Cannot find precedence and associativity for '" + opName + "'.";
        reportError(message);
      }
    }
    else if (opName.isPostfix()) {
      final int prec = 200;
      return Precedence.precedence(prec);
    }
    else if (opName.isPrefix()) {
      final int prec = 190;
      return Precedence.precedence(prec);
    }
    return null;
  }

  protected void reportError(String message)
  {
    throw new AstToPrintTreeVisitor.CannotPrintAstException(message);
  }
}
