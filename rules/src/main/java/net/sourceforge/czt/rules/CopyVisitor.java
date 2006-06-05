/*
  Copyright (C) 2005, 2006 Petra Malik
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
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * A visitor that copies a term using the given factory.  The main purpose
 * of this visitor is to create new Jokers that can be used by the prover
 * (the prover assumes that there is only one instance for each joker name).
 *
 * In addition, this visitor rewrites variable declarations with
 * multiple names into variable declarations with just one name,
 * i.e. a,b:E gets rewritten to a:E;b:E.
 *
 * @author Petra Malik
 */
public class CopyVisitor
  implements TermVisitor<Term>,
             VarDeclVisitor<Term>,
             ZDeclListVisitor<Term>,
             JokerDeclListVisitor<Term>,
             JokerExprVisitor<Term>,
             JokerDeclNameVisitor<Term>,
             JokerRefNameVisitor<Term>,
             JokerPredVisitor<Term>,
             LookupConstDeclProvisoVisitor<Term>,
             CalculateProvisoVisitor<Term>,
             TypeProvisoVisitor<Term>
{
  private Factory factory_;

  public CopyVisitor(Factory factory)
  {
    factory_ = factory;
  }

  public Term visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, false);
  }

  public Term visitVarDecl(VarDecl varDecl)
  {
    DeclNameList declNameList = (DeclNameList)
      varDecl.getDeclNameList().accept(this);
    Expr expr = (Expr) varDecl.getExpr().accept(this);
    if (declNameList instanceof ZDeclNameList) {
      ZDeclNameList zdnl = (ZDeclNameList) declNameList;
      if (zdnl.size() > 1) {
        ZDeclList zDeclList = factory_.createZDeclList();
        for (DeclName declName : zdnl) {
          ZDeclNameList list = factory_.createZDeclNameList();
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

  public Term visitJokerDeclList(JokerDeclList joker)
  {
    return factory_.createJokerDeclList(joker.getName());
  }

  public Term visitJokerExpr(JokerExpr joker)
  {
    return factory_.createJokerExpr(joker.getName());
  }

  public Term visitJokerDeclName(JokerDeclName joker)
  {
    return factory_.createJokerDeclName(joker.getName());
  }

  public Term visitJokerRefName(JokerRefName joker)
  {
    return factory_.createJokerRefName(joker.getName());
  }

  public Term visitJokerPred(JokerPred joker)
  {
    return factory_.createJokerPred(joker.getName());
  }

  public Term visitLookupConstDeclProviso(LookupConstDeclProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getLeftExpr().accept(this);
    Expr right = (Expr) proviso.getRightExpr().accept(this);
    return factory_.createLookupConstDeclProviso(context, left, right);
  }

  public Term visitCalculateProviso(CalculateProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getLeftExpr().accept(this);
    Expr right = (Expr) proviso.getRightExpr().accept(this);
    return factory_.createCalculateProviso(context, left, right);
  }

  public Term visitTypeProviso(TypeProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getExpr().accept(this);
    Expr right = (Expr) proviso.getType().accept(this);
    return factory_.createTypeProviso(context, left, right);
  }
}
