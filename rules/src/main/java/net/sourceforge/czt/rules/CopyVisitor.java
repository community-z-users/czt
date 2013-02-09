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

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * A visitor that copies a term using the given factory.  The main purpose
 * of this visitor is to create new Jokers that can be used by the prover
 * (the prover assumes that there is only one instance for each joker name).
 * <p>
 * In addition, this visitor rewrites variable declarations with
 * multiple names into variable declarations with just one name,
 * (i.e. a,b:E gets rewritten to a:E;b:E) and expands a true predicate
 * to any schema text that is missing the predicate part.
 * </p>
 * <p>
 * Finally, the setGeneralize allows you to temporarily define
 * a set of names that should be generalized into expressions,
 * usually joker expressions.  For example, this is used to
 * generalize definitions so that their type parameters become jokers.
 * </p>
 *
 * @author Petra Malik
 */
public class CopyVisitor
  implements TermVisitor<Term>,
             VarDeclVisitor<Term>,
             ZDeclListVisitor<Term>,
             ZSchTextVisitor<Term>,
             JokerDeclListVisitor<Term>,
             JokerExprVisitor<Term>,
             JokerExprListVisitor<Term>,
             JokerNameVisitor<Term>,
             JokerNameListVisitor<Term>,
             JokerPredVisitor<Term>,
	     JokerRenameListVisitor<Term>,
	     JokerStrokeVisitor<Term>,
             RefExprVisitor<Term>
{
  private Factory factory_;
  
  /**
   *  Sometimes when we copy definitions/terms, we have to
   *  generalize type parameters by converting them into jokers.
   *  This maps each type parameter onto a given expression.
   *  When this is null, no names are transformed.
   */
  private Map<ZName, Expr> generalize_;
  
  //private String generalizing_;
  
  public Map<ZName, Expr> getGeneralize()
  {
    return generalize_;
  }

  /** Set the names that should be generalized into
   *  expressions (usually joker expressions) during the copy.
   *  If this is set to null, then no names are generalized.
   *  
   *  @param why   Which definition is being unfolded (for debug messages).
   *  @param generalize
   */
  public void setGeneralize(String why, Map<ZName, Expr> generalize)
  {
    //this.generalizing_ = why;
    this.generalize_ = generalize;
  }

  public CopyVisitor()
  {
    this(new Factory(new ProverFactory()));
  }

  private static boolean checkedVisitorRules = false;
  
  public CopyVisitor(Factory factory)
  {
    factory_ = factory;
    if ( ! checkedVisitorRules ) {
      // do this check just once, rather than thousands of times.
      VisitorUtils.checkVisitorRules(this);
    }
  }

  /** This allows clients to use this copy visitor's
   *  factory to create fresh jokers.  This is typically
   *  used to set up the map for setGeneralize.
   *  
   * @param name Used as the basis for the joker name.
   * @return     A new joker expression.
   */
  public JokerExpr freshJokerExpr(String name)
  {
    return factory_.createJokerExpr(name, null);
  }

  /**
   *  Copies all the annotations from term to result.
   *  This is useful to preserve location information and type annotations etc.
   *  
   *  Those annotations that are terms are copied using this CopyVisitor,
   *  while the remaining annotations just have their reference copied across.
   *  
   * @param term   The term that is the source of the annotations.
   * @param result Where to put the annotations.
   */
  private void copyOrVisitAnns(Term term, Term result)
  {
    List<Object> anns = result.getAnns();
    for (Object o : term.getAnns()) {
      if (o instanceof Term) {
        anns.add(((Term) o).accept(this));
      }
      else {
        anns.add(o);
      }
    }
  }

  public Term visitTerm(Term term)
  {
    Term result = VisitorUtils.visitTerm(this, term, false);
    copyOrVisitAnns(term, result);
    return result;
  }

  /**
   * Expands a,b,c,...:T into a:T; b:T; c:T; ...
   */
  public Term visitVarDecl(VarDecl varDecl)
  {
    NameList declNameList = (NameList)
      varDecl.getNameList().accept(this);
    Expr expr = (Expr) varDecl.getExpr().accept(this);
    if (declNameList instanceof ZNameList) {
      ZNameList zdnl = (ZNameList) declNameList;
      if (zdnl.size() > 1) {
        ZDeclList zDeclList = factory_.createZDeclList();
        for (Name declName : zdnl) {
          ZNameList list = factory_.createZNameList();
          list.add(declName);
          zDeclList.add(factory_.createVarDecl(list, expr));
        }
        return zDeclList;
      }
    }
    return factory_.createVarDecl(declNameList, expr);
  }

  public Term visitZDeclList(ZDeclList zDeclList)
  {
    ZDeclList result = factory_.createZDeclList();
    for (Decl decl : zDeclList) {
      Term term = decl.accept(this);
      if (term instanceof ZDeclList) {
        result.addAll((ZDeclList) term);
      }
      else {
        result.add((Decl) term);
      }
    }
    return result;
  }

  public Term visitZSchText(ZSchText zSchText)
  {
    ZSchText result = factory_.createZSchText();
    result.setDeclList((DeclList) zSchText.getDeclList().accept(this));
    Pred pred = zSchText.getPred();
    if (pred != null) pred = (Pred) pred.accept(this);
    if (pred == null) pred = factory_.createTruePred();
    result.setPred(pred);
    copyOrVisitAnns(zSchText, result);
    return result;
  }

  public Term visitJokerDeclList(JokerDeclList joker)
  {
    return factory_.createJokerDeclList(joker.getName(), joker.getId());
  }

  public Term visitJokerExpr(JokerExpr joker)
  {
    return factory_.createJokerExpr(joker.getName(), joker.getId());
  }

  public Term visitJokerExprList(JokerExprList joker)
  {
    return factory_.createJokerExprList(joker.getName(), joker.getId());
  }

  public Term visitJokerName(JokerName joker)
  {
    return factory_.createJokerName(joker.getName(), joker.getId());
  }

  public Term visitJokerNameList(JokerNameList joker)
  {
    return factory_.createJokerNameList(joker.getName(), joker.getId());
  }

  public Term visitJokerPred(JokerPred joker)
  {
    return factory_.createJokerPred(joker.getName(), joker.getId());
  }

  public Term visitJokerRenameList(JokerRenameList joker)
  {
    return factory_.createJokerRenameList(joker.getName(), joker.getId());
  }

  public Term visitJokerStroke(JokerStroke joker)
  {
    return factory_.createJokerStroke(joker.getName(), joker.getId());
  }

  public Term visitRefExpr(RefExpr expr)
  {
    if (expr.getName() instanceof ZName) {
      ZName name = (ZName) expr.getName();
      if (generalize_ != null && generalize_.containsKey(name)) {
        Expr result = generalize_.get(name);
        //String msg = "copy visitor for " + generalizing_ +
        //  " transforms type " + name + " to expr "+result;
        // System.out.println(msg);
        return result; 
      }
    }
    return visitTerm(expr);
  }
}
