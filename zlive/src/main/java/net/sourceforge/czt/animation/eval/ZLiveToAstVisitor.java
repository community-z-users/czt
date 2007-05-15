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

import java.util.List;

import net.sourceforge.czt.animation.eval.flatpred.FlatConst;
import net.sourceforge.czt.animation.eval.flatpred.FlatEquals;
import net.sourceforge.czt.animation.eval.flatpred.FlatMult;
import net.sourceforge.czt.animation.eval.flatpred.FlatNegate;
import net.sourceforge.czt.animation.eval.flatpred.FlatPlus;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatConstVisitor;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatEqualsVisitor;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatMultVisitor;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatNegateVisitor;
import net.sourceforge.czt.animation.eval.flatvisitor.FlatPlusVisitor;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;

/**
 * Converts an AST containing classes that are internal to zlive
 * and converts it into a standard Z AST.
 * TODO:  this class is currently unused and incomplete.
 *        It will need to have lots of visit methods added before
 *        it is usable.
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
    List<ZName> children = flatConst.getArgs();
    Expr leftExpr = factory_.createRefExpr(children.get(0));
    Expr rightExpr = (Expr) children.get(1);
    return factory_.createEquality(leftExpr, rightExpr);
  }

  public Object visitFlatEquals(FlatEquals flatEquals)
  {
    List<ZName> children = flatEquals.getArgs();
    Expr leftExpr = factory_.createRefExpr(children.get(0));
    Expr rightExpr = factory_.createRefExpr(children.get(1));
    return factory_.createEquality(leftExpr, rightExpr);
  }
/*
  public Object visitFlatLessThan(FlatLessThan less)
  {
    try {
      List<ZName> children = less.getArgs();
      ZName a = children.get(0);
      ZName b = children.get(1);
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.LESS, null, infix);
      ZName refName = factory_.createZName(opName.getWord(), null);
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
      List<ZName> children = lt.getArgs();
      ZName a = children.get(0);
      ZName b = children.get(1);
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.LEQ, null, infix);
      ZName refName = factory_.createZName(opName.getWord(), null);
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
      List<ZName> children = flatMult.getArgs();
      ZName a = children.get(0);
      ZName b = children.get(1);
      ZName c = children.get(2);
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.MULT, null, infix);
      ZName refName = factory_.createZName(opName.getWord(), null);
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
      List<ZName> children = flatNegate.getArgs();
      ZName a = children.get(0);
      ZName b = children.get(1);
      final OperatorName.Fixity fix = OperatorName.Fixity.PREFIX;
      OperatorName opName = new OperatorName(ZString.NEG, null, fix);
      ZName refName = factory_.createZName(opName.getWord(), null);
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
      List<ZName> children = flatPlus.getArgs();
      ZName a = children.get(0);
      ZName b = children.get(1);
      ZName c = children.get(2);
      final OperatorName.Fixity infix = OperatorName.Fixity.INFIX;
      OperatorName opName = new OperatorName(ZString.PLUS, null, infix);
      ZName refName = factory_.createZName(opName.getWord(), null);
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
