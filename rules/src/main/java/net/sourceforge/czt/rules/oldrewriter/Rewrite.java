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
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.prover.SimpleProver;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.LetExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.ExprVisitor;
import net.sourceforge.czt.z.visitor.LetExprVisitor;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.z.visitor.SchTextVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * <p>A rewrite engine for Z terms.</p>
 *
 * <p>Given a set or rules and a term (AST), this engine rewrites the
 * term using the rules.  It rewrites each level of the term in a
 * top-down or, if a flag is set, bottom-up fashion.
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
  private RewriteOnceVisitor rewriter_;

  /** Maximum number of rewrites of the same expr/pred.
   *  If more rules than this are used, we assume that
   *  there is an infinite loop in the rules.
   */
  private int MAX_REWRITES = 20;

  private SectionManager manager_;

  private RuleTable rules_;

  private boolean bottomUp_ = false;

  public Rewrite(SectionManager manager, RuleTable rules)
  {
    manager_ = manager;
    rules_ = rules;
  }

  public Rewrite(SectionManager manager, RuleTable rules, String section)
  {
    this(manager, rules);
    rewriter_ =
      new RewriteOnceVisitor(createProver(rules, manager, section));
  }

  public void setBottomUp(boolean bottomUp)
  {
    bottomUp_ = bottomUp;
  }

  private SimpleProver createProver(RuleTable rules,
                                    SectionManager manager,
                                    String sectionname)
  {
    try {
      return new SimpleProver(rules, manager, sectionname);
    }
    catch (CommandException exception)
    {
      String msg = "Cannot create prover for " + sectionname;
      throw new RuntimeException(msg, exception);
    }
  }

  public Term visitZSect(ZSect zSect)
  {
    SimpleProver prover = createProver(rules_, manager_, zSect.getName());
    rewriter_ = new RewriteOnceVisitor(prover);
    return VisitorUtils.visitTerm(this, zSect, true);
  }

  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Term visitExpr(Expr expr)
  {
    if (bottomUp_) {
      return rewrite((Expr) visitChildren(expr));
    }
    return visitChildren(rewrite(expr));
  }

  protected Expr rewrite(Expr expr)
  {
    Expr result = expr;
    Expr oldExpr = expr;
    // apply rules until no more changes
    int rewrites = 0;
    do {
      oldExpr = result;
      try {
        result = (Expr) rewriter_.rewrite(result);
      }
      catch (UnboundJokerException e) {
        throw new RuntimeException(e);
      }
      rewrites++;
      if (rewrites > MAX_REWRITES) {
        throw new RuntimeException("Infinite loop in rules on expr "+result);
      }
    } while (! result.equals(oldExpr));
    return result;
  }

  protected Term visitChildren(Expr expr)
  {
    // now recurse into subexpressions
    if (expr instanceof LetExpr) {
      // special case for LET, that rewrites only the RHS of ConstDecls
      return visitLetExpr((LetExpr) expr);
    }
    else
      return VisitorUtils.visitTerm(this, expr, true);
  }

  public Term visitPred(Pred pred)
  {
    if (bottomUp_) {
      return rewrite((Pred) visitChildren(pred));
    }
    return visitChildren(rewrite(pred));
  }

  protected Pred rewrite(Pred pred)
  {
    Pred result = pred;
    Pred oldPred = pred;
    // apply rules until no more changes
    int rewrites = 0;
    do {
      oldPred = result;
      try {
        result = (Pred) rewriter_.rewrite(result);
      }
      catch (UnboundJokerException e) {
        throw new RuntimeException(e);
      }
      rewrites++;
      if (rewrites > MAX_REWRITES) {
        throw new RuntimeException("Infinite loop in rules on pred "+result);
      }
    } while (! result.equals(oldPred));
    return result;
  }

  protected Term visitChildren(Pred pred)
  {
    return VisitorUtils.visitTerm(this, pred, true);
  }

  /** For LET expressions, we rewrite only the expressions, rather
   *  than the whole schema text because let expressions can only
   *  contain constant declarations and a general rewrite rule might
   *  transform a constant into a variable declaration.
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

  /** This rewrites schema text, using rules with conclusions of the
   *  form [D1|P1] \schemaEquals [D2|P2].  Applies the first matching
   *  rule that succeeds, and does this just once to ensure
   *  termination.
   */
  public Term visitSchText(SchText schText)
  {
    if (bottomUp_) {
      return rewrite((SchText) visitChildren(schText));
    }
    return visitChildren(rewrite(schText));
  }

  protected SchText rewrite(SchText schText)
  {
    try {
      return (SchText) rewriter_.rewrite(schText);
    }
    catch (UnboundJokerException e) {
      throw new RuntimeException(e);
    }
  }

  protected Term visitChildren(SchText schText)
  {
    return VisitorUtils.visitTerm(this, schText, true);
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
