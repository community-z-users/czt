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
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.session.*;
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
    status_ = Status.UNKNOWN;
  }

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

  public static class AddDeclListVisitor
    implements SchExprVisitor<DeclList>,
               ZSchTextVisitor<DeclList>,
               DeclConsPairVisitor<DeclList>,
               EmptyDeclListVisitor<DeclList>,
               JokerDeclListVisitor<DeclList>
  {
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
}
