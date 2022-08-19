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

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;

/**
 * At the end of the typechecker, this checker visits any previously
 * unresolved ThetaExpr, SetExprs, and RefExprs (expressions that may
 * introduce a variable type into their type, or may have undeclared
 * names) to ensure that all implicit parameters have been determined
 * and all names declared.
 */
public class PostChecker
  extends Checker<ErrorAnn>
  implements ThetaExprVisitor<ErrorAnn>,
             ExprPredVisitor<ErrorAnn>,
             RefExprVisitor<ErrorAnn>,
             SetExprVisitor<ErrorAnn>
{
  public PostChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public ErrorAnn visitThetaExpr(ThetaExpr thetaExpr)
  {
    TypeAnn typeAnn = thetaExpr.getAnn(TypeAnn.class);
    Type type = typeAnn.getType();
    if (type instanceof SchemaType) {
      //check that each name in the signature is present in the
      //environment
      Signature signature = schemaType(type).getSignature();
      List<NameTypePair> pairs = signature.getNameTypePair();
      for (NameTypePair pair : pairs) {
        //if the name is not in the environment, raise an error
        Object undecAnn = pair.getZName().getAnn(UndeclaredAnn.class);
        if (undecAnn != null) {
          ZName decorName = factory().createZName(pair.getZName(), true);
          decorName.getZStrokeList().addAll(thetaExpr.getZStrokeList());
          Object [] params = {decorName, thetaExpr};
          ErrorAnn errorAnn =
            errorAnn(thetaExpr,
                     ErrorMessage.UNDECLARED_IDENTIFIER_IN_EXPR,
                     params);
          boolean added = addErrorAnn(thetaExpr, errorAnn);
          return added ? errorAnn : null;
        }
      }
    }
    else {
      assert false : type;
    }
    return null;
  }

  public ErrorAnn visitExprPred(ExprPred exprPred)
  {
    TypeAnn typeAnn = exprPred.getExpr().getAnn(TypeAnn.class);
    Type type = typeAnn.getType();
    if (type instanceof PowerType &&
        powerType(type).getType() instanceof SchemaType) {
      //check that each name in the signature is present in the
      //environment
      PowerType powerType = (PowerType) type;
      Signature signature = schemaType(powerType.getType()).getSignature();
      List<NameTypePair> pairs = signature.getNameTypePair();
      for (NameTypePair pair : pairs) {
        //if the name is not in the environment, raise an error
        Object undecAnn = pair.getZName().getAnn(UndeclaredAnn.class);
        if (undecAnn != null) {
          Object [] params = {pair.getZName(), exprPred};
          ErrorAnn errorAnn =
            errorAnn(exprPred,
                     ErrorMessage.UNDECLARED_IDENTIFIER_IN_EXPR,
                     params);
          boolean added = addErrorAnn(exprPred, errorAnn);
          return added ? errorAnn : null;
        }
      }
    }
    else {
      assert false : type;
    }
    return null;
  }

  public ErrorAnn visitRefExpr(RefExpr refExpr)
  {
    ZName zName = refExpr.getZName();
    UndeclaredAnn uAnn = zName.getAnn(UndeclaredAnn.class);
    ParameterAnn pAnn = refExpr.getAnn(ParameterAnn.class);

    final boolean nameIsUndeclared = uAnn != null;
    if (nameIsUndeclared) {
      ErrorAnn errorAnn = createUndeclaredNameError(zName);

      //if use before declaration is not enabled, or if it is but this
      //is the second pass over the specification, remove the
      //undeclared annotation
      if (!useBeforeDecl() || sectTypeEnv().getSecondTime()) {
	removeAnn(zName, uAnn);
      }

      //if this ref expr was created for an ExprPred
      ExprPred exprPred = zName.getAnn(ExprPred.class);
      boolean added = false;
      if (exprPred == null) {
        added = addErrorAnn(zName, errorAnn);
      }
      else {
        added = addErrorAnn(exprPred, errorAnn);
        removeAnn(zName, exprPred);
        Object ann = exprPred.getAnn(ParameterAnn.class);
        removeAnn(exprPred, ann);
      }
      return added ? errorAnn : null;
    }
    //check that no types in the list are still unresolved
    else if (pAnn != null) {
      List<Type2> gParams = pAnn.getParameters();
      List<Expr> exprs = factory().list();
      for (Type2 type : gParams) {
        try {
          Expr expr = (Expr) type.accept(carrierSet());
          assert expr != null;
          exprs.add(expr);
        }
        catch (UndeterminedTypeException e) {
          Object [] params = {refExpr};
          ErrorAnn errorAnn =
            errorAnn(refExpr, ErrorMessage.PARAMETERS_NOT_DETERMINED, params);
          boolean added = addErrorAnn(refExpr, errorAnn);
          removeAnn(refExpr, pAnn);
          return added ? errorAnn : null;
        }
      }
      refExpr.getZExprList().addAll(exprs);
      removeAnn(refExpr, pAnn);
    }
    return null;
  }

  public ErrorAnn visitSetExpr(SetExpr setExpr)
  {
    //get the type from the annotations
    Type2 type = getType2FromAnns(setExpr);
    assert type instanceof PowerType : type;
    try {
      Expr expr = (Expr) type.accept(carrierSet());
      assert expr != null;
    }
    catch (UndeterminedTypeException e) {
      Object [] params = {setExpr};
      ErrorAnn errorAnn =
        errorAnn(setExpr, ErrorMessage.PARAMETERS_NOT_DETERMINED, params);
      boolean added = addErrorAnn(setExpr, errorAnn);
      return added ? errorAnn : null;
    }
    return null;
  }
}
