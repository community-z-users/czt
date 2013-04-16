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
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A <code>PredChecker</code> instance visits the Pred instances in an
 * AST, checks the preds for type consistencies, adding an ErrorAnn if
 * there are inconsistencies.
 *
 * Each visit method returns a <code>UResult</code>, which indicates
 * that the types in the predicate have been partially unified, or
 * not.
 */
public class PredChecker
  extends Checker<UResult>
  implements QntPredVisitor<UResult>,
             Pred2Visitor<UResult>,
             AndPredVisitor<UResult>,
             MemPredVisitor<UResult>,
             NegPredVisitor<UResult>,
             ExprPredVisitor<UResult>,
             PredVisitor<UResult>
{
  public PredChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  /**
   * Any "left over" predicates.
   */
  public UResult visitPred(Pred pred)
  {
    return SUCC;
  }

  /**
   * Exists1Pred, ExistsPred, and ForallPred instances are
   * visited as an instance of their super class QntPred.
   */
  public UResult visitQntPred(QntPred qntPred)
  {
    UResult result = SUCC;

    //enter a new variable scope
    typeEnv().enterScope();

    //visit the SchText
    SchText schText = qntPred.getSchText();
    schText.accept(schTextChecker());

    //visit the Pred
    Pred pred = qntPred.getPred();
    UResult unified = pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (unified == PARTIAL) {
      result = pred.accept(predChecker());
    }

    //exit the variable scope
    typeEnv().exitScope();

    return result;
  }

  /**
   * IffPred, ImpliesPred, and OrPred instances are
   * visited as an instance of their super class Pred2.
   */
  public UResult visitPred2(Pred2 pred2)
  {
    //visit the left and right preds
    Pred leftPred = pred2.getLeftPred();
    UResult lSolved = leftPred.accept(predChecker());

    Pred rightPred = pred2.getRightPred();
    UResult rSolved = rightPred.accept(predChecker());

    //if either the left or right are partially solved, then
    //this predicate is also partially solved
    UResult result = UResult.conj(lSolved, rSolved);

    return result;
  }

  /**
   * AndPred instances are visited separately from Pred2 instances
   * because they have extra requires if they are a chain relation.
   */
  public UResult visitAndPred(AndPred andPred)
  {
    //UResult result = SUCC;

    //visit the left and right preds
    Pred leftPred = andPred.getLeftPred();
    UResult lSolved = leftPred.accept(predChecker());

    Pred rightPred = andPred.getRightPred();
    UResult rSolved = rightPred.accept(predChecker());
    UResult result = checkChainRelOp(andPred);

    //if either the left or right are partially solved, then
    //this predicate is also partially solved
    UResult solved = UResult.conj(lSolved, rSolved);
    result = UResult.conj(solved, result);

    return result;
  }

  public UResult visitMemPred(MemPred memPred)
  {
    //visit the left and right expressions
    Expr leftExpr = memPred.getLeftExpr();
    Type2 leftType = leftExpr.accept(exprChecker());

    Expr rightExpr = memPred.getRightExpr();
    Type2 rightType = rightExpr.accept(exprChecker());

    //unify the left and right side of the membership predicate
    PowerType powerType = factory().createPowerType(leftType);
    UResult unified = unify(powerType, rightType);
    if (unified == FAIL) {
      Type2 rightBaseType = getBaseType(rightType);
      //if this pred is an equality
      boolean mixfix = memPred.getMixfix().booleanValue();
      if (mixfix && rightExpr instanceof SetExpr) {
        Object [] params = {memPred, leftType, rightBaseType};
        error(memPred, ErrorMessage.TYPE_MISMATCH_IN_EQUALITY, params);
      }
      //if this is a membership
      else if (!mixfix) {
        Object [] params = {memPred, leftType, rightType};
        error(memPred, ErrorMessage.TYPE_MISMATCH_IN_MEM_PRED, params);
      }
      //if it a relation other than equals or membership
      else {
        if (!instanceOf(rightType, PowerType.class) &&
            !instanceOf(rightType, VariableType.class)) {
          Object [] params = {rightExpr, memPred, rightType};
          error(memPred, ErrorMessage.NAME_NOT_REL_OP, params);
        }
        else if (instanceOf(rightType, PowerType.class)) {
          Type2 innerType = powerType(rightType).getType();
          if (instanceOf(innerType, ProdType.class)) {
            assert instanceOf(leftType, ProdType.class);
            ProdType leftProdType = (ProdType) leftType;
            ProdType rightProdType = (ProdType) innerType;
            for (int i = 0; i < leftProdType.getType().size(); i++) {
              Type2 nextLeft = (Type2) leftProdType.getType().get(i);
              Type2 nextRight = (Type2) rightProdType.getType().get(i);
              UResult nextUnified = unify(nextLeft, nextRight);
              if (nextUnified == FAIL) {
                Object [] params = {i + 1, memPred, nextLeft, nextRight};
                error(memPred, ErrorMessage.TYPE_MISMATCH_IN_REL_OP, params);
              }
            }
          }
          else if (!instanceOf(innerType, VariableType.class)) {
            assert !instanceOf(leftType, ProdType.class);
            Object [] params = {1, memPred, leftType, innerType};
            error(memPred, ErrorMessage.TYPE_MISMATCH_IN_REL_OP, params);
          }
        }
      }
    }

    return unified;
  }

  public UResult visitNegPred(NegPred negPred)
  {
    //visit the predicate
    Pred pred = negPred.getPred();
    UResult result = pred.accept(predChecker());
    return result;
  }

  public UResult visitExprPred(ExprPred exprPred)
  {
    //visit the expression
    Expr expr = exprPred.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //check that the expr is a schema expr
    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);

    UResult result = unify(vPowerType, exprType);
    if (result == FAIL) {
      Object [] params = {exprPred, exprType};
      error(exprPred, ErrorMessage.NON_SCHEXPR_IN_EXPR_PRED, params);
    }
    //check that the names referenced in this expression are declared
    //in the environment
    else {
      SchemaType schemaType = (SchemaType) vPowerType.getType();
      Signature signature = schemaType.getSignature();
      if (!instanceOf(signature, VariableSignature.class)) {
        List<NameTypePair> pairs = signature.getNameTypePair();
        for (int i = 0; i < pairs.size(); i++ ) {
          NameTypePair pair = pairs.get(i);
	  Name zName =  pair.getName();

          //lookup the type of this name in the environment
          Type envType = getType(zName);

          Object undecAnn = zName.getAnn(UndeclaredAnn.class);
          //if the name is undeclared, copy the annotation to the name
          //in the signature
          if (undecAnn != null) {
            pair.getZName().getAnns().add(undecAnn);
            if (!containsObject(paraErrors(), exprPred)) {
              addTermForPostChecking(exprPred);
            }
          }
          else {
            removeAnn(pair.getZName(), UndeclaredAnn.class);
          }

          //if the type of the name in the current environment does
          //not unify with the type in the expr, raise an error
          Type2 typeA = unwrapType(envType);
          Type2 typeB = unwrapType(pair.getType());
          UResult unified = unify(typeA, typeB);
          result = UResult.conj(result, unified);
          if (unified == FAIL) {
            Object [] params = {zName, typeA, typeB};
            error(exprPred, ErrorMessage.TYPE_MISMATCH_IN_SIGNATURE, params);
          }
        }
      }
    }

    return result;
  }
}
