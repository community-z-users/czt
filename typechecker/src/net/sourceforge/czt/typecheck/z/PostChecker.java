/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * At the end of the typechecker, this checker visits any previously
 * unresolved SetExprs and RefExprs (expressions that may introduce a
 * variable type into their type) to ensure that all implicit
 * parameters have been determined.
 */
class PostChecker
  extends Checker
  implements RefExprVisitor,
             SetExprVisitor
{
  //the position of the current error/term
  protected int position_;

  //calculates the carrier set for a type
  protected CarrierSet carrierSet = new CarrierSet();

  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    position_ = 0;
  }

  public void postCheck()
  {
    for (position_ = 0; position_ < errors().size(); position_++) {
      Object next = errors().get(position_);
      if (next instanceof Expr) {
        Expr expr = (Expr) next;
        expr.accept(this);
      }
    }
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    RefName refName = refExpr.getRefName();
    UndeclaredAnn uAnn = (UndeclaredAnn) refName.getAnn(UndeclaredAnn.class);
    ParameterAnn pAnn = (ParameterAnn) refExpr.getAnn(ParameterAnn.class);

    //check if this name is undeclared
    if (uAnn != null) {
      ErrorAnn message = errorFactory().undeclaredIdentifier(refName);
      errors().set(position_, message);
      removeAnn(refName, uAnn);

      //if this ref expr was created for a
      ExprPred exprPred = (ExprPred) refName.getAnn(ExprPred.class);
      if (exprPred == null) {
        addAnn(refName, message);
      }
      else {
        addAnn(exprPred, message);
        removeAnn(refName, exprPred);
        Object ann = (ParameterAnn) exprPred.getAnn(ParameterAnn.class);
        removeAnn(exprPred, ann);
      }
      return null;
    }
    // check that no types in the list are still unresolved
    else if (pAnn != null) {
      List params = pAnn.getParameters();
      List exprs = new ArrayList();
      for (Iterator iter = params.iterator(); iter.hasNext(); ) {
        Type2 type = (Type2) iter.next();
        try {
          Expr expr = (Expr) type.accept(carrierSet);
          exprs.add(expr);
        }
        catch (UndeterminedTypeException e) {
          ErrorAnn message = errorFactory().parametersNotDetermined(refExpr);
          errors().set(position_, message);
          addAnn(refExpr, message);
          removeAnn(refExpr, pAnn);
          return null;
        }
      }
      refExpr.getExpr().addAll(exprs);
      removeAnn(refExpr, pAnn);
    }

    //if there is no error, remove this from the list
    //decrementing position to allow for the removed item
    errors().remove(position_--);
    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    //get the type from the annotations
    Type2 type = getTypeFromAnns(setExpr);

    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      Type2 innerType = powerType.getType();

      //if the inner type is not resolved, then replace the expr with an
      //error annotation
      if (resolve(innerType) instanceof VariableType) {
        ErrorAnn message = errorFactory().parametersNotDetermined(setExpr);
        errors().set(position_, message);
        addAnn(setExpr, message);
        return null;
      }
    }

    //if there is no error, remove this from the list
    //decrementing position to allow for the removed item
    errors().remove(position_--);
    return null;
  }
}
