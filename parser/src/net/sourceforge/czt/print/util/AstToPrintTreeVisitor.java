/*
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

package net.sourceforge.czt.print.util;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.visitor.*;

public class AstToPrintTreeVisitor
  implements TermVisitor,
             ApplExprVisitor,
             RefExprVisitor
{
  public Object visitTerm(Term term)
  {
    return VisitorUtils.visitTerm(this, term, true);
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
    if (applExpr.getMixfix().booleanValue()) {
      RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
      OperatorName opName = refExpr.getRefName().getOperatorName();
      Expr args = (Expr) applExpr.getRightExpr().accept(this);
      List argList = new ArrayList();
      if (opName.isUnary()) {
        argList.add(args);
      }
      else {
        TupleExpr tuple = (TupleExpr) args;
        argList.addAll(tuple.getExpr());
      }
      return new OperatorApplication(opName, argList);
    }
    Application appl = new Application();
    appl.setLeftExpr((Expr) applExpr.getLeftExpr().accept(this));
    appl.setRightExpr((Expr) applExpr.getRightExpr().accept(this));
    return appl;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    if (refExpr.getMixfix().booleanValue()) {
      return new OperatorApplication(refExpr.getRefName().getOperatorName(),
                                     (ListTerm) refExpr.getExpr().accept(this));
    }
    return VisitorUtils.visitTerm(this, refExpr, true);
  }
}
