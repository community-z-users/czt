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
          //  implements ClassUnionExprVisitor,
             //PolyExprVisitor,
             //PredExprVisitor,
             //BindSelExprVisitor
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
  /*
  public Object visitClassUnionExpr(ClassUnionExpr classUnionExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr lExpr = (Expr) classUnionExpr.getLeftExpr();
    Expr rExpr = (Expr) classUnionExpr.getRightExpr();
    Type2 lType = (Type2) lExpr.accept(this);
    Type2 rType = (Type2) rExpr.accept(this);

    ClassRefType vlClassRefType = factory().createClassRefType();
    PowerType vlPowerType = factory().createPowerType(vlClassRefType);
    ClassRefType vrClassRefType = factory().createClassRefType();
    PowerType vrPowerType = factory().createPowerType(vrClassRefType);

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
      List<ClassRef> classes = list(getClasses(vlPowerType.getType()));
      parents.addAll(getClasses(vrPowerType.getType()));
      Signature state = factory().createSignature();
      ClassSig cSig =
        factory().createClassSig(classes, state, list(), list());
      ClassUnionType classUnionType = factory().createClassUnionType(cSig);
      type = factory().createPowerType(classUnionType);
    }

    //add the type annotation
    addTypeAnn(classUnionExpr, type);

    return type;
  }


  public Object visitPolyExpr(PolyExpr polyExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr expr = polyExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(this);

    //if the left expr is not a class description, raise an error
    ClassRefType vClassRefType = factory().createClassRefType();
    PowerType vPowerType = factory().createPowerType(vClassRefType);
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
      ClassSig cSig = vClassRefType.getClassSig();
      if (!instanceOf(cSig, VariableClassSig.class)) {
        ClassRef cName = vClassRefType.getThisClass();
        List<RefName> subClasses = list(cName);

        //find any subclasses
        List<NameSectTypeTriple> triples =
          sectTypeEnv().getNameSectTypeTriple();
        for (NameSectTypeTriple triple : triples) {

          Type2 subClassRefType = unwrapType(triple.getType());
          if (isClassExpr(subClassRefType)) {
            ClassRefType classType = (ClassRefType) powerType(subClassRefType).getType();
            ClassSig subClassSig = classType.getClassSig();

            //if the type is a subclass, try to add it to the subclass list
            //if (subClassSig.getClassName() != null &&
            //    subClassSig.getParentClass().contains(cName)) {

              //the subclasses must have the same number of parameters as
              //the "top-level" class
              ClassRef subRef = classType.getThisClass();
              if (triple.getType() instanceof GenericType) {
                GenericType gType = (GenericType) triple.getType();
                final int superSize = refExpr.getExpr().size();
                final int subSize = gType.getName().size();
                if (superSize != subSize) {
                  Object [] params = {subRef, superSize, subSize};
                  error(polyExpr,
                        ErrorMessage.PARAMETER_MISMATCH_IN_POLYEXPR, params);
                }
              }
              subClasses.add(subRef);
              //}
          }
        }
        ClassSig polySig =
          factory().createClassSig(subClasses, cSig.getState(),
                                   cSig.getAttribute(),
                                   cSig.getOperation());
        ClassPolyType polyClass = factory().createClassPolyType(polySig);
        type = factory().createPowerType(polyClass);
      }
    }

    //add the type annotation
    addTypeAnn(polyExpr, type);

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

    //add the type annotation
    addTypeAnn(predExpr, type);

    return type;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    Type2 type = factory().createUnknownType();

    //get the type of the expression
    Expr expr = bindSelExpr.getExpr();
    Type2 exprType = (Type2) expr.accept(exprChecker());

    if (!instanceOf(exprType, VariableType.class)) {
      if (exprType instanceof SchemaType) {
        type = (Type2) zExprChecker_.visitBindSelExpr(bindSelExpr);
      }
      else if (exprType instanceof ClassRefType) {

      }
      else {
        Object [] params = {bindSelExpr, exprType};
        error(bindSelExpr, ErrorMessage.NON_BINDING_IN_BINDSELEXPR, params);
      }
    }

    //add the type annotation
    addTypeAnn(bindSelExpr, type);

    return type;
  }
*/
}
