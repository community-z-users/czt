/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.rules.oldrewriter;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.prover.Prover;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.rewriter.Rewriter;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.StrokeList;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.z.visitor.SchTextVisitor;
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * Returns a rewritten version of the given term.  Note
 * that this is not recursive, i.e. the children of the term
 * are not rewritten.  If the rewriting fails, the apply method
 * returns the given term itself while the visit methods return
 * <code>null</code>.  Note also that the term returned by the
 * visit methods may contain jokers.
 */
public class RewriteOnceVisitor
  implements Rewriter,
             TermVisitor<Term>,
             ExprVisitor<Term>,
             PredVisitor<Term>,
             SchTextVisitor<Term>
{
  /** The name of the schema text equality operator: schemaEquals. */
  private RefExpr schemaEqualsRefExpr_;

  private Prover prover_;

  public RewriteOnceVisitor(Prover prover)
  {
    prover_ = prover;
    Factory factory = new Factory(new ProverFactory());
    String schemaEqOp = ZString.ARG_TOK + "schemaEquals" + ZString.ARG_TOK;
    StrokeList noStrokes = factory.createZStrokeList();
    ZName name = factory.createZName(schemaEqOp, noStrokes, "global");
    schemaEqualsRefExpr_ = factory.createRefExpr(name);
  }

  public Term rewrite(Term term)
    throws UnboundJokerException
  {
    Term result = term.accept(this);
    if (result != null) return ProverUtils.removeJoker(result);
    return term;
  }

  public Term visitTerm(Term term)
  {
    return term;
  }

  /**
   * Returns a rewritten version of the given expression by trying to
   * prove <code>expr = JokerExpr</code> using the prover.
   */
  public Term visitExpr(Expr expr)
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerExpr joker = (ProverJokerExpr)
      factory.createJokerExpr("_", null);
    Pred pred = factory.createEquality(expr, joker);
    Sequent sequent = factory.createSequent();
    sequent.setPred(pred);
    if (prover_.prove(sequent)) {
      return joker.boundTo();
    }
    return null;
  }

  /**
   * Returns a rewritten version of the given predicate by trying to
   * prove <code>pred \iff JokerPred</code> using the given prover.
   */
  public Term visitPred(Pred pred)
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerPred joker = (ProverJokerPred)
      factory.createJokerPred("_", null);
    Sequent sequent = factory.createSequent();
    sequent.setPred(factory.createIffPred(pred, joker));
    if (prover_.prove(sequent)) {
      return joker.boundTo();
    }
    return null;
  }

  /**
   * Returns a rewritten version of the given schema text by trying to prove
   * <code>schText schemaEquals result</code> using the given prover.
   */
  public Term visitSchText(SchText schText)
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerExpr joker = (ProverJokerExpr)
      factory.createJokerExpr("_", null);
    // now create the predicate: schText \schemaEquals joker
    // System.out.println("Rewriting schtext: "+schText);
    Expr original = factory.createSchExpr(schText);
    TupleExpr pair = factory.createTupleExpr(original, joker);
    Pred pred =
      factory.createMemPred(pair, schemaEqualsRefExpr_, Boolean.TRUE);
    Sequent sequent = factory.createSequent();
    sequent.setPred(pred);
    if (prover_.prove(sequent)) {
      Expr newExpr = (Expr) joker.boundTo();
      if (newExpr instanceof SchExpr) {
        SchText result = ((SchExpr) newExpr).getSchText();
        return result;
      }
      else {
        final String msg = "Incorrect schemaEquals rule returned: " + newExpr;
        throw new RuntimeException(msg);
      }
    }
    return null;
  }
}
