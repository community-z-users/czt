package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * A <code>PredChecker</code> instance visits the Pred instances in an
 * AST, checks the preds for type consistencies, adding an ErrorAnn if
 * there are inconsistencies.
 *
 * Each visit method returns a <code>UResult</code>, which indicates
 * that the types in the predicate have been partially unified, or
 * not.
 */
class PredChecker
  extends Checker
  implements QntPredVisitor,
             Pred2Visitor,
             AndPredVisitor,
             MemPredVisitor,
             NegPredVisitor,
             ExprPredVisitor,
             PredVisitor
{
  public PredChecker(CheckerInfo info)
  {
    super(info);
  }

  /**
   * Any "left over" predicates
   */
  public Object visitPred(Pred pred)
  {
    return SUCC;
  }

  /**
   * Exists1Pred, ExistsPred, and ForallPred instances are
   * visited as an instance of their super class QntPred.
   */
  public Object visitQntPred(QntPred qntPred)
  {
    UResult result = SUCC;

    //enter a new variable scope
    typeEnv().enterScope();

    //visit the SchText
    SchText schText = qntPred.getSchText();
    schText.accept(exprChecker());

    //visit the Pred
    Pred pred = qntPred.getPred();
    UResult unified = (UResult) pred.accept(this);

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (unified == PARTIAL) {
      result = (UResult) pred.accept(this);
    }

    //exit the variable scope
    typeEnv().exitScope();

    return result;
  }

  /**
   * IffPred, ImpliesPred, and OrPred instances are
   * visited as an instance of their super class Pred2.
   */
  public Object visitPred2(Pred2 pred2)
  {
    UResult result = SUCC;

    //visit the left and right preds
    Pred leftPred = pred2.getLeftPred();
    UResult lSolved = (UResult) leftPred.accept(this);

    Pred rightPred = pred2.getRightPred();
    UResult rSolved = (UResult) rightPred.accept(this);

    //if either the left or right are partially solved, then
    //this predicate is also partially solved
    if (lSolved == PARTIAL || rSolved == PARTIAL) {
      result = PARTIAL;
    }

    return result;
  }

  /**
   * AndPred instances are visited separately from Pred2 instances
   * because they have extra requires if they are a chain relation.
   */
  public Object visitAndPred(AndPred andPred)
  {
    UResult result = SUCC;

    //visit the left and right preds
    Pred leftPred = andPred.getLeftPred();
    UResult lSolved = (UResult) leftPred.accept(this);

    Pred rightPred = andPred.getRightPred();
    UResult rSolved = (UResult) rightPred.accept(this);

    //if this is a chain relation, unify the RHS of the left pred
    //with the LHS of the right predicate
    if (Op.Chain.equals(andPred.getOp())) {
      Type2 rhsLeft = getRightType(leftPred);
      Type2 lhsRight = getLeftType(rightPred);
      UResult unified = unify(rhsLeft, lhsRight);

      //if the lhs and rhs do not unify, raise an error
      if (unified == FAIL) {
        ErrorAnn message =
          errorFactory().typeMismatchInChainRelation(andPred,
                                                     rhsLeft,
                                                     lhsRight);
        error(andPred, message);
      }
      else if (unified == PARTIAL) {
        result = PARTIAL;
      }
    }

    //if either the left or right are partially solved, then
    //this predicate is also partially solved
    if (lSolved == PARTIAL || rSolved == PARTIAL) {
      result = PARTIAL;
    }

    return result;
  }

  public Object visitMemPred(MemPred memPred)
  {
    UResult result = SUCC;

    //visit the left and right expressions
    Expr leftExpr = memPred.getLeftExpr();
    Type2 leftType = (Type2) leftExpr.accept(exprChecker());

    Expr rightExpr = memPred.getRightExpr();
    Type2 rightType = (Type2) rightExpr.accept(exprChecker());

    //unify the left and right side of the membership predicate
    PowerType powerType = factory().createPowerType(leftType);
    UResult unified = unify(powerType, rightType);

    if (unified == FAIL) {
      Type2 rightBaseType = getBaseType(rightType);
      //if this pred is an equality
      boolean mixfix = memPred.getMixfix().booleanValue();
      if (mixfix && rightExpr instanceof SetExpr) {
        ErrorAnn message =
          errorFactory().typeMismatchInEquality(memPred,
                                                leftType,
                                                rightBaseType);
        error(memPred, message);
      }
      //if this is a membership
      else if (!mixfix) {
        ErrorAnn message =
          errorFactory().typeMismatchInMemPred(memPred, leftType, rightType);
        error(memPred, message);
      }
      //if it a relation other than equals or membership
      else {
        ErrorAnn message = errorFactory().typeMismatchInRelOp(memPred,
                                                              leftType,
                                                              rightBaseType);
        error(memPred, message);
      }
    }
    else if (unified == PARTIAL) {
      result = PARTIAL;
    }

    return result;
  }

  public Object visitNegPred(NegPred negPred)
  {
    //visit the predicate
    Pred pred = negPred.getPred();
    UResult result = (UResult) pred.accept(this);
    return result;
  }

  public Object visitExprPred(ExprPred exprPred)
  {
    UResult result = SUCC;

    //visit the expression
    Expr expr = exprPred.getExpr();
    Type2 type = (Type2) expr.accept(exprChecker());

    //check that the expr is a schema expr
    SchemaType vSchemaType = factory().createSchemaType();
    PowerType vPowerType = factory().createPowerType(vSchemaType);
    if (unify(vPowerType, type) == FAIL) {
      ErrorAnn message =
        errorFactory().nonSchExprInExprPred(exprPred, type);
      error(exprPred, message);
    }
    return result;
  }

  /////////////// helper methods ///////////////////////
  protected Type2 getLeftType(Pred pred)
  {
    MemPred memPred = (MemPred) pred;
    List types = getLeftRightType(memPred);
    Type2 result = (Type2) types.get(0);
    return result;
  }

  protected Type2 getRightType(Pred pred)
  {
    Type2 result = null;

    if (pred instanceof MemPred) {
      MemPred memPred = (MemPred) pred;
      List types = getLeftRightType(memPred);
      result = (Type2) types.get(1);
    }
    else if (pred instanceof AndPred) {
      AndPred andPred = (AndPred) pred;
      MemPred memPred = (MemPred) andPred.getRightPred();
      result = getRightType(memPred);
    }

    return result;
  }

  protected List getLeftRightType(MemPred memPred)
  {
    List result = list();

    Expr leftExpr = memPred.getLeftExpr();
    Expr rightExpr = memPred.getRightExpr();

    //if this pred is an equality
    boolean mixfix = memPred.getMixfix().booleanValue();
    if (mixfix && rightExpr instanceof SetExpr) {
      result.add(getTypeFromAnns(leftExpr));
      result.add(getBaseType(getTypeFromAnns(rightExpr)));
    }
    //if this is a membership
    else if (!mixfix) {
      result.add(getTypeFromAnns(leftExpr));
      result.add(getTypeFromAnns(rightExpr));
    }
    //if this is a relation
    else {
      if (leftExpr instanceof TupleExpr) {
        TupleExpr tupleExpr = (TupleExpr) leftExpr;
        result.add(getTypeFromAnns((Expr) tupleExpr.getExpr().get(0)));
        result.add(getTypeFromAnns((Expr) tupleExpr.getExpr().get(1)));
      }
      else {
        result.add(getTypeFromAnns(leftExpr));
      }
    }

    return result;
  }

  /**
   * Gets the base type of a power type, or returns that the type
   * is unknown.
   */
  public static Type2 getBaseType(Type2 type2)
  {
    Type2 result = unknownType();

    //if it's a PowerType, get the base type
    if (isPowerType(type2)) {
      PowerType powerType = (PowerType) type2;
      result = powerType.getType();
    }
    else if (isUnknownType(type2)) {
      result = type2;
    }

    return result;
  }
}
