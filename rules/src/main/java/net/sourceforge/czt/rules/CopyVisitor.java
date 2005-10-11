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
 * A visitor that copies a term and uses the given factory to create
 * new Joker.
 *
 * @author Petra Malik
 */
public class CopyVisitor
  implements TermVisitor,
             JokerDeclListVisitor,
             ZDeclListVisitor,
             HeadDeclListVisitor,
             JokerExprVisitor,
             JokerDeclNameVisitor,
             JokerRefNameVisitor,
             JokerPredVisitor,
             LookupConstDeclProvisoVisitor,
             CalculateProvisoVisitor
{
  private Factory factory_;

  public CopyVisitor(Factory factory)
  {
    factory_ = factory;
  }

  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, false);
  }

  public Object visitJokerDeclList(JokerDeclList joker)
  {
    return factory_.createJokerDeclList(joker.getName());
  }

  public Object visitZDeclList(ZDeclList zDeclList)
  {
    return transform(zDeclList.iterator(), new EmptyDeclListImpl());
  }

  public Object visitHeadDeclList(HeadDeclList hdl)
  {
    return transform(hdl.getZDeclList().iterator(),
                     (DeclList) hdl.getJokerDeclList().accept(this));
  }

  /**
   * Doesn't visit the last argument.
   */
  private DeclList transform(Iterator<Decl> iter, DeclList last)
  {
    if (iter.hasNext()) {
      Decl decl = (Decl) iter.next().accept(this);
      DeclList cdr = transform(iter, last);
      return new DeclConsPairImpl(decl, cdr);
    }
    return last;
  }

  public Object visitJokerExpr(JokerExpr joker)
  {
    return factory_.createJokerExpr(joker.getName());
  }

  public Object visitJokerDeclName(JokerDeclName joker)
  {
    return factory_.createJokerDeclName(joker.getName());
  }

  public Object visitJokerRefName(JokerRefName joker)
  {
    return factory_.createJokerRefName(joker.getName());
  }

  public Object visitJokerPred(JokerPred joker)
  {
    return factory_.createJokerPred(joker.getName());
  }

  public Object visitLookupConstDeclProviso(LookupConstDeclProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getLeftExpr().accept(this);
    Expr right = (Expr) proviso.getRightExpr().accept(this);
    return factory_.createLookupConstDeclProviso(context, left, right);
  }

  public Object visitCalculateProviso(CalculateProviso proviso)
  {
    SequentContext context = proviso.getSequentContext();
    Expr left = (Expr) proviso.getLeftExpr().accept(this);
    Expr right = (Expr) proviso.getRightExpr().accept(this);
    return factory_.createCalculateProviso(context, left, right);
  }
}
