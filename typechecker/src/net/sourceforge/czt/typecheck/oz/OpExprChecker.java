/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.util.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.oz.impl.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.typecheck.z.*;

/**
 * An <code>OpChecker</code> instance visits the OpExprs instances in
 * an AST, checks them for type consistencies, adding an ErrorAnn
 * if there are inconsistencies.
 *
 * Each visit method to OpExpr objects return the signature of the
 * expression.
 */
public class OpExprChecker
  extends Checker
  implements
      AnonOpExprVisitor,
      OpPromotionExprVisitor,
      OpTextVisitor,
      OpExprVisitor
{
  public OpExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  public Object visitOpExpr(OpExpr opExpr)
  {
    return factory().createSignature();
  }


  public Object visitAnonOpExpr(AnonOpExpr anonOpExpr)
  {
    //get the signature of the operation text
    OpText opText = anonOpExpr.getOpText();
    Signature signature = (Signature) opText.accept(opExprChecker());
    return signature;
  }

  public Object visitOpText(OpText opText)
  {
    //enter a new variable scope
    typeEnv().enterScope();

    //get the class signature for "self"
    ClassType selfType = getSelfType();
    ClassSig selfSig = selfType.getClassSig();

    //check that each name in the delta list is a primary variable
    List<RefName> deltaList = opText.getDelta();
    for (RefName delta : deltaList) {
      DeclName declName = factory().createDeclName(delta);
      if (!primary().contains(declName)) {
        Object [] params = {delta};
        error(delta, ErrorMessage.NON_PRIMDECL_IN_DELTALIST, params);
      }
    }

    //visit the schema text and gets its signature
    SchText schText = opText.getSchText();
    Signature signature = (Signature) schText.accept(exprChecker());

    //exit the variable scope
    typeEnv().exitScope();

    return signature;
  }

  public Object visitOpPromotionExpr(OpPromotionExpr opPromExpr)
  {
    Signature signature = factory().createVariableSignature();

    //if the expression is null, then we use "self" as the instance
    Expr expr = opPromExpr.getExpr();
    if (expr == null) {
      RefName refName = factory().createRefName(OzString.SELF, list(), null);
      expr = factory().createRefExpr(refName, list(), Boolean.FALSE);
    }

    //get the type of the expression
    Type2 exprType = (Type2) expr.accept(exprChecker());

    VariableClassType vClassType = factory().createVariableClassType();
    vClassType.complete();
    UResult unified = unify(vClassType, exprType);
    //if the type is not a class type, raise an error
    if (unified == FAIL) {
      Object [] params = {opPromExpr, exprType};
      error(opPromExpr, ErrorMessage.NON_CLASS_IN_OPPROMEXPR, params);
    }
    else {
      ClassSig cSig = vClassType.getClassSig();
      if (!instanceOf(cSig, VariableClassSig.class)) {
        RefName refName = opPromExpr.getName();
        Signature opSig = findOperation(refName, cSig);
        if (opSig == null) {
          Object [] params = {opPromExpr};
          error(opPromExpr, ErrorMessage.NON_EXISTENT_NAME_IN_OPPROMEXPR, params);
        }
        else {
          signature = opSig;
        }
      }
    }

    return signature;
  }
}
