/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/

package net.sourceforge.czt.animation.eval;

import net.sourceforge.czt.animation.eval.flatpred.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZString;

/**
 * Converts an AST containing classes that are internal to zlive
 * and converts it into a standard Z AST.
 */
public class ZLiveToAstVisitor
  implements TermVisitor,
             FlatConstVisitor,
             FlatEqualsVisitor,
             FlatMultVisitor,
             FlatNegateVisitor,
             FlatPlusVisitor
{
  private Factory factory_ = new Factory();

  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Object visitFlatConst(FlatConst flatConst)
  {
    Object[] children = flatConst.getChildren();
    Expr leftExpr = factory_.createRefExpr((RefName) children[0]);
    Expr rightExpr = (Expr) children[1];
    return factory_.createEquality(leftExpr, rightExpr);
  }

  public Object visitFlatEquals(FlatEquals flatEquals)
  {
    Object[] children = flatEquals.getChildren();
    Expr leftExpr = factory_.createRefExpr((RefName) children[0]);
    Expr rightExpr = factory_.createRefExpr((RefName) children[1]);
    return factory_.createEquality(leftExpr, rightExpr);
  }
/*
  public Object visitFlatLessThan(FlatLessThan less)
  {
    try {
      Object[] children = less.getChildren();
      RefName a = (RefName) children[0];
      RefName b = (RefName) children[1];
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.LESS, null, infix);
      RefName refName = factory_.createRefName(opName.getWord(), null);
      Expr pair = factory_.createTupleExpr(factory_.createRefExpr(a),
                                 factory_.createRefExpr(b));
      return factory_.createFunOpAppl(refName, pair);
    }
    catch(OperatorName.OperatorNameException e) {
      throw new CztException("This should never happen", e);
    }
  }

  public Object visitFlatLessThanEquals(FlatLessThanEquals lt)
  {
    try {
      Object[] children = lt.getChildren();
      RefName a = (RefName) children[0];
      RefName b = (RefName) children[1];
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.LEQ, null, infix);
      RefName refName = factory_.createRefName(opName.getWord(), null);
      Expr pair = factory_.createTupleExpr(factory_.createRefExpr(a),
                                 factory_.createRefExpr(b));
      return factory_.createFunOpAppl(refName, pair);
    }
    catch(OperatorName.OperatorNameException e) {
      throw new CztException("This should never happen", e);
    }
  }
*/
  public Object visitFlatMult(FlatMult flatMult)
  {
    try {
      Object[] children = flatMult.getChildren();
      RefName a = (RefName) children[0];
      RefName b = (RefName) children[1];
      RefName c = (RefName) children[2];
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.MULT, null, infix);
      RefName refName = factory_.createRefName(opName.getWord(), null);
      Expr pair = factory_.createTupleExpr(factory_.createRefExpr(a),
                                 factory_.createRefExpr(b));
      Expr leftExpr = factory_.createFunOpAppl(refName, pair);
      RefExpr rightExpr = factory_.createRefExpr(c);
      return factory_.createEquality(leftExpr, rightExpr);
    }
    catch(OperatorName.OperatorNameException e) {
      throw new CztException("This should never happen", e);
    }
  }

  public Object visitFlatNegate(FlatNegate flatNegate)
  {
    try {
      Object[] children = flatNegate.getChildren();
      RefName a = (RefName) children[0];
      RefName b = (RefName) children[1];
      final OperatorName.Fixity fix = OperatorName.Fixity.PREFIX;
      OperatorName opName = new OperatorName(ZString.NEG, null, fix);
      RefName refName = factory_.createRefName(opName.getWord(), null);
      Expr leftExpr = factory_.createFunOpAppl(refName,
                                               factory_.createRefExpr(a));
      RefExpr rightExpr = factory_.createRefExpr(b);
      return factory_.createEquality(leftExpr, rightExpr);
    }
    catch(OperatorName.OperatorNameException e) {
      throw new CztException("This should never happen", e);
    }
  }

  public Object visitFlatPlus(FlatPlus flatPlus)
  {
    try {
      Object[] children = flatPlus.getChildren();
      RefName a = (RefName) children[0];
      RefName b = (RefName) children[1];
      RefName c = (RefName) children[2];
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.PLUS, null, infix);
      RefName refName = factory_.createRefName(opName.getWord(), null);
      Expr pair = factory_.createTupleExpr(factory_.createRefExpr(a),
                                 factory_.createRefExpr(b));
      Expr leftExpr = factory_.createFunOpAppl(refName, pair);
      RefExpr rightExpr = factory_.createRefExpr(c);
      return factory_.createEquality(leftExpr, rightExpr);
    }
    catch(OperatorName.OperatorNameException e) {
      throw new CztException("This should never happen", e);
    }
  }
}
