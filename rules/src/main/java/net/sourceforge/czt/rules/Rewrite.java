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

package net.sourceforge.czt.rules;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.LetExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.StrokeList;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.LetExprVisitor;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.z.visitor.SchTextVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zpatt.ast.Sequent;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * <p>A rewrite engine for Z terms.</p>
 *
 * <p>Given a set or rules and a term (AST), this engine rewrites the
 * term using the rules.  It rewrites each level of the term in a
 * top-down fashion.
 *
 * It tries the rules in the order that they appear in the
 * specification and commits to the first matching rule.
 * If there are no matching rules, the expression is left unchanged.
 * An expression can be rewritten by several rules in succession.
 *
 * @author Petra Malik
 */
public class Rewrite
  implements TermVisitor<Term>,
             ExprVisitor<Term>,
             SchTextVisitor<Term>,
             PredVisitor<Term>,
             ZSectVisitor<Term>,
             LetExprVisitor<Term>
{
  /** Maximum number of rewrites of the same expr/pred.
   *  If more rules than this are used, we assume that
   *  there is an infinite loop in the rules.
   */
  private int MAX_REWRITES = 20;

  private Prover prover_;

  private SectionManager manager_;

  private RuleTable rules_;

  /** The name of the schema text equality operator: schemaEquals. */
  private static RefExpr schemaEqualsRefExpr_;

  public Rewrite(SectionManager manager, RuleTable rules)
  {
    VisitorUtils.checkVisitorRules(this);
    manager_ = manager;
    rules_ = rules;
    Factory factory = new Factory(new ProverFactory());
    String schemaEqOp = ZString.ARG_TOK + "schemaEquals" + ZString.ARG_TOK;
    StrokeList noStrokes = factory.createZStrokeList();
    ZName name = factory.createZName(schemaEqOp, noStrokes, "global");
    schemaEqualsRefExpr_ = factory.createRefExpr(name);
  }

  public Rewrite(SectionManager manager, RuleTable rules, String section)
  {
    this(manager, rules);
    prover_ = new SimpleProver(rules, manager, section);
  }

  public Term visitZSect(ZSect zSect)
  {
    prover_ = new SimpleProver(rules_, manager_, zSect.getName());
    return VisitorUtils.visitTerm(this, zSect, true);
  }

  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Term visitExpr(Expr expr)
  {
    Expr oldExpr = expr;
    // apply rules until no more changes
    int rewrites = 0;
    do {
      oldExpr = expr;
      try {
        expr = (Expr) rewriteOnce(expr, prover_);
      }
      catch (UnboundJokerException e) {
        throw new RuntimeException(e);
      }
      rewrites++;
      if (rewrites > MAX_REWRITES) {
        throw new RuntimeException("Infinite loop in rules on expr "+expr);
      }
    } while (! expr.equals(oldExpr));
    // now recurse into subexpressions
    if (expr instanceof LetExpr) {
      // special case for LET, that rewrites only the RHS of ConstDecls
      return visitLetExpr( (LetExpr)expr );
    }
    else
      return VisitorUtils.visitTerm(this, expr, true);
  }

  public Term visitPred(Pred pred)
  {
    Pred oldPred = pred;
    // apply rules until no more changes
    int rewrites = 0;
    do {
      oldPred = pred;
      try {
        pred = (Pred) rewriteOnce(pred, prover_);
      }
      catch (UnboundJokerException e) {
        throw new RuntimeException(e);
      }
      rewrites++;
      if (rewrites > MAX_REWRITES) {
        throw new RuntimeException("Infinite loop in rules on pred "+pred);
      }
    } while (! pred.equals(oldPred));
    // now recurse into subexpressions
    return VisitorUtils.visitTerm(this, pred, true);
  }

  /** For LET expressions, we rewrite only the expressions,
   *  rather than the whole schema text.
   * @param expr  The LET expression LET V1=E1;...Vn=En @ E
   * @return      The rewritten expression: LET V1=E1';...Vn=En' @ E'
   */
  public Term visitLetExpr(LetExpr expr)
  {
    Factory factory = new Factory(new ProverFactory());
    ZSchText stext = expr.getZSchText();
    ZDeclList newdecls = factory.createZDeclList();
    for (Decl decl : stext.getZDeclList()) {
      ConstDecl cdecl = (ConstDecl) decl;
      ConstDecl newDecl =
        factory.createConstDecl(cdecl.getName(),
            (Expr) cdecl.getExpr().accept(this));
      newdecls.add(newDecl);
    }
    ZSchText newStext = factory.createZSchText(newdecls, stext.getPred());
    Expr newExpr = (Expr) expr.getExpr().accept(this);
    return factory.createLetExpr(newStext, newExpr);
  }

  /** This rewrites schema text, using rules with conclusions
   *  of the form [D1|P1] \schemaEquals [D2|P2].
   */
  public Term visitSchText(SchText schText)
  {
    // apply the first matching rule just once.
    try {
      schText = (SchText) rewriteOnce(schText, prover_);
    }
    catch (UnboundJokerException e) {
      throw new RuntimeException(e);
    }
    // now recurse into subexpressions
    return VisitorUtils.visitTerm(this, schText, true);
  }

  /**
   * Returns a rewritten version of the given schema text by trying to prove
   * <code>schText schemaEquals result</code> using the given prover.
   * If the prover fails, the original schema text is returned.
   */
  public static SchText rewriteOnce(SchText schText, Prover prover)
    throws UnboundJokerException
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
    if (prover.prove(sequent)) {
      Expr newExpr = (Expr) ProverUtils.removeJoker(joker.boundTo());
      if (newExpr instanceof SchExpr) {
        SchText result = ((SchExpr)newExpr).getSchText(); 
        //        System.out.println("Rewrote to "+result);
        return result;
      }
      else {
        final String msg = "Incorrect schemaEquals rule returned: " + newExpr;
        throw new RuntimeException(msg);
      }
    }
    return schText;
  }

  /**
   * Returns a rewritten version of the given expression by trying to
   * prove <code>expr = JokerExpr</code> using the given prover.  Note
   * that this is not recursive, i.e. the children of the expression
   * are not rewritten.  If the prover fails, the given expression
   * itself is returned.
   */
  public static Term rewriteOnce(Expr expr, Prover prover)
    throws UnboundJokerException
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerExpr joker = (ProverJokerExpr)
      factory.createJokerExpr("_", null);
    Pred pred = factory.createEquality(expr, joker);
    Sequent sequent = factory.createSequent();
    sequent.setPred(pred);
    if (prover.prove(sequent)) {
      return ProverUtils.removeJoker(joker.boundTo());
    }
    return expr;
  }

  /**
   * Returns a rewritten version of the given predicate by trying to
   * prove <code>pred \iff JokerPred</code> using the given prover.
   * Note that this is not recursive, i.e. the children of the
   * predicate are not rewritten.  If the prover fails, the given
   * predicate itself is returned.
   */
  public static Term rewriteOnce(Pred pred, Prover prover)
    throws UnboundJokerException
  {
    Factory factory = new Factory(new ProverFactory());
    ProverJokerPred joker = (ProverJokerPred)
      factory.createJokerPred("_", null);
    Sequent sequent = factory.createSequent();
    sequent.setPred(factory.createIffPred(pred, joker));
    if (prover.prove(sequent)) {
      return ProverUtils.removeJoker(joker.boundTo());
    }
    return pred;
  }

  /**
   * Recurses into a Spec or ZSect and rewrites predicates and
   * expressions using the given rules.
   *
   * @throws NullPointerException if term is <code>null</code>.
   */
  public static Term rewrite(SectionManager manager,
                             Term term,
                             RuleTable rules)
  {
    Rewrite visitor = new Rewrite(manager, rules);
    return term.accept(visitor);
  }

  /**
   * Recurses into a term and rewrites predicates and
   * expressions using the given rules.
   *
   * @throws NullPointerException if term is <code>null</code>.
   */
  public static Term rewrite(SectionManager manager,
                             String section,
                             Term term,
                             RuleTable rules)
  {
    Rewrite visitor = new Rewrite(manager, rules, section);
    return (Term) term.accept(visitor);
  }
}
