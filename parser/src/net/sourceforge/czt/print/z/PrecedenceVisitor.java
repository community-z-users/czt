/*
  Copyright (C) 2006 Petra Malik
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
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

public class PrecedenceVisitor
  implements TermVisitor<Precedence>,
             PrintPredicateVisitor<Precedence>,
             ThetaExprVisitor<Precedence>,
             BindSelExprVisitor<Precedence>,
             TupleSelExprVisitor<Precedence>,
             RenameExprVisitor<Precedence>,
             DecorExprVisitor<Precedence>,
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
             NegPredVisitor<Precedence>,
             NegExprVisitor<Precedence>,
             AndExprVisitor<Precedence>,
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
    return new Precedence(250);
  }

  public Precedence visitBindSelExpr(BindSelExpr term)
  {
    return new Precedence(240);
  }

  public Precedence visitTupleSelExpr(TupleSelExpr term)
  {
    return new Precedence(240);
  }

  public Precedence visitRenameExpr(RenameExpr term)
  {
    return new Precedence(230);
  }

  public Precedence visitDecorExpr(DecorExpr term)
  {
    return new Precedence(220);
  }

  public Precedence visitApplication(Application term)
  {
    return new Precedence(210);
  }

  public Precedence visitOperatorApplication(OperatorApplication term)
  {
    return term.getPrecedence();
  }

  public Precedence visitPowerExpr(PowerExpr term)
  {
    return new Precedence(190);
  }

  public Precedence visitProdExpr(ProdExpr term)
  {
    return new Precedence(180, 8);
  }

  public Precedence visitPreExpr(PreExpr term)
  {
    return new Precedence(170);
  }

  public Precedence visitProjExpr(ProjExpr term)
  {
    return new Precedence(160);
  }

  public Precedence visitHideExpr(HideExpr term)
  {
    return new Precedence(150);
  }

  public Precedence visitPipeExpr(PipeExpr term)
  {
    return new Precedence(140);
  }

  public Precedence visitCompExpr(CompExpr term)
  {
    return new Precedence(130);
  }

  public Precedence visitCondExpr(CondExpr term)
  {
    return new Precedence(120);
  }

  public Precedence visitLetExpr(LetExpr term)
  {
    return new Precedence(110);
  }

  public Precedence visitMuExpr(MuExpr term)
  {
    return new Precedence(100);
  }

  public Precedence visitLambdaExpr(LambdaExpr term)
  {
    return new Precedence(90);
  }

  public Precedence visitNegPred(NegPred term)
  {
    return new Precedence(70);
  }

  public Precedence visitNegExpr(NegExpr term)
  {
    return new Precedence(70);
  }

  public Precedence visitAndExpr(AndExpr term)
  {
    return new Precedence(60);
  }

  public Precedence visitOrPred(OrPred term)
  {
    return new Precedence(50);
  }

  public Precedence visitOrExpr(OrExpr term)
  {
    return new Precedence(50);
  }

  public Precedence visitImpliesPred(ImpliesPred term)
  {
    return new Precedence(40);
  }

  public Precedence visitImpliesExpr(ImpliesExpr term)
  {
    return new Precedence(40);
  }

  public Precedence visitIffPred(IffPred term)
  {
    return new Precedence(30);
  }

  public Precedence visitIffExpr(IffExpr term)
  {
    return new Precedence(30);
  }

  public Precedence visitForallPred(ForallPred term)
  {
    return new Precedence(20);
  }

  public Precedence visitExistsPred(ExistsPred term)
  {
    return new Precedence(20);
  }

  public Precedence visitExists1Pred(Exists1Pred term)
  {
    return new Precedence(20);
  }

  public Precedence visitForallExpr(ForallExpr term)
  {
    return new Precedence(20);
  }

  public Precedence visitExistsExpr(ExistsExpr term)
  {
    return new Precedence(20);
  }

  public Precedence visitExists1Expr(Exists1Expr term)
  {
    return new Precedence(20);
  }
}
