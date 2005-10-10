/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.rules.ast;

import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.CalculateProvisoImpl;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * <p>A CalculateProviso used by the prover.</p>
 *
 * @author Petra Malik
 */
public class ProverCalculateProviso
  extends CalculateProvisoImpl
  implements ProverProviso
{
  private Status status_ = Status.UNCHECKED;

  public void check(SectionManager manager, String section)
  {
    final Expr expr = getRightExpr();

    // schema declaration merge
    if (expr instanceof ApplExpr) {
      final ApplExpr applExpr = (ApplExpr) expr;
      final Expr leftExpr = applExpr.getLeftExpr();
      final Expr rightExpr = applExpr.getRightExpr();
      final boolean mixfix = applExpr.getMixfix();
      if (! mixfix && leftExpr instanceof SchExpr &&
          rightExpr instanceof ApplExpr) {
        final SchExpr leftSchExpr = (SchExpr) leftExpr;
        final ApplExpr applExpr2 = (ApplExpr) rightExpr;
        final Expr leftExpr2 = applExpr2.getLeftExpr();
        final Expr rightExpr2 = applExpr2.getRightExpr();
        final boolean mixfix2 = applExpr2.getMixfix();
        if (! mixfix2 && leftExpr2 instanceof RefExpr &&
            rightExpr2 instanceof SchExpr) {
          final RefExpr refExpr = (RefExpr) leftExpr2;
          final SchExpr rightSchExpr = (SchExpr) rightExpr2;
          final RefName refName = refExpr.getRefName();
          if (refName instanceof ZRefName) {
            final ZRefName zRefName = (ZRefName) refName;
            if ("schemamerge".equals(zRefName.getWord())) {
              SchExpr result = merge(leftSchExpr, rightSchExpr);
              Set<Binding> bindings = new HashSet<Binding>();
              if (result != null &&
                  Unification.unify(result, getLeftExpr(), bindings)) {
                status_ = Status.PASS;
                return;
              }
              else {
                status_ = Status.FAIL;
                return;
              }
            }
          }
        }
      }
    }
    else if (expr instanceof DecorExpr) {
      final DecorExpr decorExpr = (DecorExpr) expr;
      final Stroke stroke = decorExpr.getStroke();
      if (decorExpr.getExpr() instanceof SchExpr) {
        final SchExpr schExpr = (SchExpr) decorExpr.getExpr();
        final CollectStateVariablesVisitor collectVisitor =
          new CollectStateVariablesVisitor();
        schExpr.getZSchText().getDeclList().accept(collectVisitor);
        final DecorateNamesVisitor visitor =
          new DecorateNamesVisitor(collectVisitor.getVariables(), stroke);
        try {
          Expr result = (Expr) decorExpr.getExpr().accept(visitor);
          Set<Binding> bindings = new HashSet<Binding>();
          Unification unifier = new Unification(bindings);
          if (result != null &&
              unifier.unify(result, getLeftExpr())) {
            status_ = Status.PASS;
            return;
          }
          status_ = Status.FAIL;
          return;
        }
        catch(CztException e) {
          // status is unknown
        }
      }
    }
    status_ = Status.UNKNOWN;
  }

  /**
   * Merges the declaration lists of the given schema expressions.
   */
  private SchExpr merge(SchExpr left, SchExpr right)
  {
    final Factory factory = new Factory(new ProverFactory());
    DeclList declList = new EmptyDeclListImpl();
    declList = right.accept(new AddDeclListVisitor(declList));
    if (declList == null) return null;
    declList = left.accept(new AddDeclListVisitor(declList));
    if (declList == null) return null;
    return factory.createSchExpr(factory.createZSchText(declList,
                      factory.createTruePred()));
  }

  public Status getStatus()
  {
    return status_;
  }

  /**
   * Appends a given declaration list to the declaration list
   * contained in the visited prover AST.
   */
  public static class AddDeclListVisitor
    implements SchExprVisitor<DeclList>,
               ZSchTextVisitor<DeclList>,
               DeclConsPairVisitor<DeclList>,
               EmptyDeclListVisitor<DeclList>,
               JokerDeclListVisitor<DeclList>
  {
    /**
     * The declartion list to be appended.
     */
    private DeclList declList_;

    public AddDeclListVisitor(DeclList declList)
    {
      declList_ = declList;
    }

    public DeclList visitSchExpr(SchExpr schExpr)
    {
      return schExpr.getSchText().accept(this);
    }

    public DeclList visitZSchText(ZSchText zSchText)
    {
      return zSchText.getDeclList().accept(this);
    }

    public DeclList visitDeclConsPair(DeclConsPair pair)
    {
      DeclList declList = pair.cdr().accept(this);
      if (declList != null) {
        return new DeclConsPairImpl(pair.car(), declList);
      }
      return null;
    }

    public DeclList visitEmptyDeclList(EmptyDeclList empty)
    {
      return declList_;
    }

    public DeclList visitJokerDeclList(JokerDeclList jokerDeclList)
    {
      if (jokerDeclList instanceof ProverJokerDeclList) {
        Joker joker = (Joker) jokerDeclList;
        Term boundTo = joker.boundTo();
        if (boundTo != null) return boundTo.accept(this);
      }
      return null;
    }
  }

  public static class CollectStateVariablesVisitor
    implements ConstDeclVisitor,
               VarDeclVisitor,
               EmptyDeclListVisitor,
               DeclConsPairVisitor,
               JokerDeclListVisitor
  {
    private Set<DeclName> variables_ = new HashSet<DeclName>();

    public Set<DeclName> getVariables()
    {
      return variables_;
    }

    public Object visitEmptyDeclList(EmptyDeclList emptyDeclList)
    {
      return null;
    }

    public Object visitDeclConsPair(DeclConsPair pair)
    {
      pair.car().accept(this);
      pair.cdr().accept(this);
      return null;
    }

    public Object visitVarDecl(VarDecl varDecl)
    {
      for (DeclName declName : varDecl.getDeclName()) {
        variables_.add(declName);
      }
      return null;
    }

    public Object visitConstDecl(ConstDecl constDecl)
    {
      variables_.add(constDecl.getDeclName());
      return null;
    }

    public Object visitJokerDeclList(JokerDeclList jokerDeclList)
    {
      if (jokerDeclList instanceof Joker) {
        Joker joker = (Joker) jokerDeclList;
        Term boundTo = joker.boundTo();
        if (boundTo != null) {
          return boundTo.accept(this);
        }
      }
      throw new CztException("Found unbound Joker");
    }
  }

  public static class DecorateNamesVisitor
    implements TermVisitor<Term>,
               ZDeclNameVisitor<Term>,
               ZRefNameVisitor<Term>
  {
    private Set<DeclName> declNames_;

    /**
     * The stroke to be added to names.
     */
    private Stroke stroke_;

    public DecorateNamesVisitor(Set<DeclName> declNames, Stroke stroke)
    {
      declNames_ = declNames;
      stroke_ = stroke;
    }

    public Term visitTerm(Term term)
    {
      if (term instanceof Joker) {
        Joker joker = (Joker) term;
        Term boundTo = joker.boundTo();
        if (boundTo != null) {
          return boundTo.accept(this);
        }
        throw new CztException("Found unbound Joker");
      }
      return (Term) VisitorUtils.visitTerm(this, term, true);
    }

    public Term visitZDeclName(ZDeclName zDeclName)
    {
      Object[] children = zDeclName.getChildren();
      for (int i = 0; i < children.length; i++) {
        if (children[i] instanceof Term) {
          children[i] = ((Term) children[i]).accept(this);
        }
      }
      ZDeclName newName = (ZDeclName) zDeclName.create(children);
      if (declNames_.contains(zDeclName)) {
        newName.getStroke().add(stroke_);
      }
      return newName;
    }

    public Term visitZRefName(ZRefName zRefName)
    {
      Object[] children = zRefName.getChildren();
      for (int i = 0; i < children.length; i++) {
        if (children[i] instanceof Term) {
          children[i] = ((Term) children[i]).accept(this);
        }
      }
      ZRefName newName = (ZRefName) zRefName.create(children);
      if (declNames_.contains(zRefName.getDecl())) {
        newName.getStroke().add(stroke_);
      }
      return newName;
    }
  }
}
