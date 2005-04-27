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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * At the end of the typechecker, this checker visits any previously
 * unresolved SetExprs and RefExprs (expressions that may introduce a
 * variable type into their type) to ensure that all implicit
 * parameters have been determined.
 */
public class PostChecker
  extends Checker
  implements ThetaExprVisitor,
	     RefExprVisitor,
             SetExprVisitor
{
  //calculates the carrier set for a type
  protected CarrierSet carrierSet_ = null;

  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    carrierSet_ = new CarrierSet();
  }

  public Object visitThetaExpr(ThetaExpr thetaExpr)
  {
    TypeAnn typeAnn = (TypeAnn) thetaExpr.getAnn(TypeAnn.class);
    Type type = typeAnn.getType();
    if (type instanceof SchemaType) {
      //check that each name in the signature is present in the
      //environment
      Signature signature = schemaType(type).getSignature();
      List<NameTypePair> pairs = signature.getNameTypePair();
      for (NameTypePair pair : pairs) {
	//if the name is not in the environment, raise an error
	Object undecAnn = pair.getName().getAnn(UndeclaredAnn.class);
	if (undecAnn != null) {
	  DeclName decorName = factory().createDeclName(pair.getName());
	  decorName.getStroke().addAll(thetaExpr.getStroke());
	  Object [] params = {decorName, thetaExpr};
	  ErrorAnn errorAnn =
	    errorAnn(thetaExpr, 
		     ErrorMessage.UNDECLARED_IDENTIFIER_IN_EXPR, params);
	  addAnn(thetaExpr, errorAnn);
	  return errorAnn;
	}
      }
    }

    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    RefName refName = refExpr.getRefName();
    UndeclaredAnn uAnn = (UndeclaredAnn) refName.getAnn(UndeclaredAnn.class);
    ParameterAnn pAnn = (ParameterAnn) refExpr.getAnn(ParameterAnn.class);

    //check if this name is undeclared
    if (uAnn != null) {
      Object [] params = {refName};
        ErrorAnn errorAnn =
          errorAnn(refName, ErrorMessage.UNDECLARED_IDENTIFIER, params);
      removeAnn(refName, uAnn);

      //if this ref expr was created for an ExprPred
      ExprPred exprPred = (ExprPred) refName.getAnn(ExprPred.class);
      if (exprPred == null) {
        addAnn(refName, errorAnn);
      }
      else {
        addAnn(exprPred, errorAnn);
        removeAnn(refName, exprPred);
        Object ann = (ParameterAnn) exprPred.getAnn(ParameterAnn.class);
        removeAnn(exprPred, ann);
      }
      return errorAnn;
    }
    //check that no types in the list are still unresolved
    else if (pAnn != null) {
      List<Type2> gParams = pAnn.getParameters();
      List<Expr> exprs = list();
      for (Type2 type : gParams) {
        try {
          Expr expr = (Expr) type.accept(carrierSet_);
          assert expr != null;
          exprs.add(expr);
        }
        catch (UndeterminedTypeException e) {
          Object [] params = {refExpr};
          ErrorAnn errorAnn =
            errorAnn(refExpr, ErrorMessage.PARAMETERS_NOT_DETERMINED, params);
          addAnn(refExpr, errorAnn);
          removeAnn(refExpr, pAnn);
          return errorAnn;
        }
      }
      refExpr.getExpr().addAll(exprs);
      removeAnn(refExpr, pAnn);
    }

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
        Object [] params = {setExpr};
        ErrorAnn errorAnn =
          errorAnn(setExpr, ErrorMessage.PARAMETERS_NOT_DETERMINED, params);
        addAnn(setExpr, errorAnn);
        return errorAnn;
      }
    }
    return null;
  }
}
