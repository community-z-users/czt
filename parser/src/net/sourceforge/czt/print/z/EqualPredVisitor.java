/**
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.util.List;
import java.util.ArrayList;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.visitor.*;

/**
 * <p>
 * A MemPred visitor that transforms the default representation
 * of equality to a representation via relational operator.
 * </p>
 *
 * <p>
 * In the standard AST, equality is represented via containment in a set,
 * i.e. 'a = b' is a member predicate (MemPred) with Mixfix == "true",
 * with a reference expression (RefExpr) with word 'a' as its first (left)
 * expression, and with a set expression (SetExpr) of a reference
 * expression with word b as its second (right) expression.  This is
 * difficult to handle by visitors that print the AST, for instance
 * in latex markup, since equality must be handled differently from other
 * relational operators.
 * </p>
 *
 * <p>
 * This class transforms the representation of equality described above
 * into the one used for all other relational operators: a member
 * predicate (MemPred) with Mixfix == "true", a tuple expression (TupleExpr)
 * as its first (left) expression, and a reference expression with word
 * ' _ = _ ' as its second (right) expression.  Note that this is not
 * standard conform since equality is part of the language and not defined as
 * relational operator.
 *
 * @author Petra Malik
 */
public class EqualPredVisitor
  implements MemPredVisitor,
             TermVisitor,
             TermAVisitor
{
  ZFactory factory_ = new ZFactoryImpl();

  public EqualPredVisitor()
  {
  }

  public EqualPredVisitor(ZFactory factory)
  {
    factory_ = factory;
  }

  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Object visitTermA(TermA termA)
  {
    TermA newTermA = (TermA) visitTerm(termA);
    if (newTermA != termA) {
      newTermA.getAnns().addAll(termA.getAnns());
    }
    return newTermA;
  }

  public Object visitMemPred(MemPred memPred)
  {
    boolean mixfix = memPred.getMixfix().booleanValue();
    Expr firstExpr = (Expr) visit(memPred.getLeftExpr());
    Expr secondExpr = (Expr) visit(memPred.getRightExpr());
    if (mixfix && secondExpr instanceof SetExpr) {
      SetExpr setExpr = (SetExpr) secondExpr;
      if (setExpr.getExpr().size() != 1) {
        String message = "Unexpected Mixfix == true.";
        message += "\n  Fixing it to Mixfix == false.";
        System.err.println(message);
        return factory_.createMemPred(firstExpr,
                                      secondExpr,
                                      Boolean.valueOf(false));
      }
      List exprList = new ArrayList();
      exprList.add(firstExpr);
      exprList.add(setExpr.getExpr().get(0));
      TupleExpr tupleExpr = factory_.createTupleExpr(exprList);
      RefName refName = factory_.createRefName(" _ = _ ", null, null);
      RefExpr refExpr = factory_.createRefExpr(refName,
                                               null,
                                               Boolean.valueOf(false));
      MemPred newMemPred = factory_.createMemPred(tupleExpr,
                                                 refExpr,
                                                 Boolean.valueOf(true));
      return newMemPred;
    }
    if (firstExpr != memPred.getLeftExpr() ||
        secondExpr != memPred.getRightExpr()) {
      return factory_.createMemPred(firstExpr,
                                    secondExpr,
                                    Boolean.valueOf(mixfix));
    }
    return memPred;
  }

  private Object visit(Object object)
  {
    if (object instanceof Term) {
      return ((Term) object).accept(this);
    }
    return object;
  }
}
