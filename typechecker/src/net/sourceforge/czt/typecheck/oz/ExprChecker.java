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

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.typecheck.z.*;

/**
 * An <code>ExprChecker</code> instance visits the Exprs instances in
 * an AST, checks them for type consistencies, adding an ErrorAnn
 * if there are inconsistencies.
 *
 * Each visit method to Expr objects return the type (Type2) of the
 * expression.
 */
public class ExprChecker
  extends Checker
  implements ClassUnionExprVisitor,
             PolyExprVisitor,
             PredExprVisitor
{
  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.ExprChecker zExprChecker_;

  public ExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zExprChecker_ =
      new net.sourceforge.czt.typecheck.z.ExprChecker(typeChecker);
  }

  public Object visitTerm(Term term)
  {
    return term.accept(zExprChecker_);
  }

  public Object visitClassUnionExpr(ClassUnionExpr classUnionExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr lExpr = (Expr) classUnionExpr.getLeftExpr();
    Expr rExpr = (Expr) classUnionExpr.getRightExpr();
    Type2 lType = (Type2) lExpr.accept(this);
    Type2 rType = (Type2) rExpr.accept(this);

    ClassType vlClassType = factory().createClassType();
    PowerType vlPowerType = factory().createPowerType(vlClassType);
    ClassType vrClassType = factory().createClassType();
    PowerType vrPowerType = factory().createPowerType(vrClassType);

    UResult lUnified = unify(vlPowerType, lType);
    UResult rUnified = unify(vrPowerType, rType);
    //if the left expr is not a class description, raise an error
    if (lUnified == FAIL) {
      Object [] params = {classUnionExpr, lType};
      error(classUnionExpr, ErrorMessage.NON_CLASS_IN_CLASSUNIONEXPR, params);
    }

    //if the right expr is not a class description, raise an error
    if (rUnified == FAIL) {
      Object [] params = {classUnionExpr, rType};
      error(classUnionExpr, ErrorMessage.NON_CLASS_IN_CLASSUNIONEXPR, params);
    }

    if (lUnified != FAIL && rUnified != FAIL) {
      List<RefName> parents = list(getClasses(vlPowerType.getType()));
      parents.addAll(getClasses(vrPowerType.getType()));
      ClassSignature cSig =
        factory().createClassSignature(null, null, null, parents,
                                       list(), list(), list());
      ClassType classType = factory().createClassType(cSig);
      type = factory().createPowerType(classType);
    }
    return type;
  }

  public Object visitPolyExpr(PolyExpr polyExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr expr = polyExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    //if the left expr is not a class description, raise an error
    ClassType vClassType = factory().createClassType();
    PowerType vPowerType = factory().createPowerType(vClassType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a class type, raise an error
    if (unified == FAIL) {
      Object [] params = {polyExpr, exprType};
      error(polyExpr, ErrorMessage.NON_CLASS_IN_POLYEXPR, params);
    }
    else if (!instanceOf(expr, RefExpr.class)) {
      Object [] params = {polyExpr};
      error(polyExpr, ErrorMessage.NON_REF_IN_POLYEXPR, params);
    }
    else {
      RefExpr refExpr = (RefExpr) expr;
      ClassSignature cSig = vClassType.getClassSignature();
      if (!instanceOf(cSig, VariableClassSignature.class)) {
        RefName cName = factory().createRefName(cSig.getClassName());
        List<RefName> subClasses = list(cName);

        //find any subclasses
        List<NameSectTypeTriple> triples =
          sectTypeEnv().getNameSectTypeTriple();
        for (NameSectTypeTriple triple : triples) {

          Type2 subClassType = unwrapType(triple.getType());
          if (isClassExpr(subClassType)) {
            ClassType classType = (ClassType) powerType(subClassType).getType();
            ClassSignature subClassSig = classType.getClassSignature();

            //if the type is a subclass, try to add it to the subclass list
            if (subClassSig.getClassName() != null &&
                subClassSig.getParentClass().contains(cName)) {

              //the subclasses must have the same number of parameters as
              //the "top-level" class
              if (triple.getType() instanceof GenericType) {
                GenericType gType = (GenericType) triple.getType();
                final int superSize = refExpr.getExpr().size();
                final int subSize = gType.getName().size();
                if (superSize != subSize) {
                  DeclName subClassName = subClassSig.getClassName();
                  Object [] params = {cName, superSize, subClassName, subSize};
                  error(polyExpr,
                        ErrorMessage.PARAMETER_MISMATCH_IN_POLYEXPR, params);
                }
              }
              RefName subName = factory().createRefName(subClassSig.getClassName());
              subClasses.add(subName);
            }
          }
        }
        ClassSignature polySig =
          factory().createClassSignature(null,
                                         cSig.getPrimaryDecl(),
                                         cSig.getSecondaryDecl(),
                                         subClasses,
                                         cSig.getAttribute(),
                                         cSig.getOperation(),
                                         cSig.getVisibility());
        ClassType polyClass = factory().createClassType(polySig);
        type = factory().createPowerType(polyClass);
      }
    }

    return type;
  }

  public Object visitPredExpr(PredExpr predExpr)
  {
    Type2 type = factory().createUnknownType();

    //visit the predicate
    Pred pred = predExpr.getPred();
    UResult solved = (UResult) pred.accept(predChecker());

    if (solved == SUCC) {
      //if this is a true or false literal, raise an error
      if (pred instanceof Fact) {
        Object [] params = {pred};
        error(pred, ErrorMessage.FACT_AS_EXPR, params);
      }

      //create a boolean type
      type = factory().createBoolType();
    }
    return type;
  }
}
