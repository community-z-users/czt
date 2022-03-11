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

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;
import static net.sourceforge.czt.z.util.ZUtils.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * An <code>ExprChecker</code> instance visits the Exprs instances in
 * an AST, checks them for type consistencies, adding an ErrorAnn
 * if there are inconsistencies.
 *
 * Each visit method to Expr objects return the type (Type2) of the
 * expression.
 */
public class ExprChecker
  extends Checker<Type2>
  implements
    ClassUnionExprVisitor<Type2>,
    PolyExprVisitor<Type2>,
    ContainmentExprVisitor<Type2>,
    PredExprVisitor<Type2>,
    BindSelExprVisitor<Type2>,
    RenameExprVisitor<Type2>
{
  //a Z expr checker
  protected net.sourceforge.czt.typecheck.z.ExprChecker zExprChecker_;

  public ExprChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zExprChecker_ =
      new net.sourceforge.czt.typecheck.z.ExprChecker(typeChecker);
  }

  public Type2 visitTerm(Term term)
  {
    return term.accept(zExprChecker_);
  }

  public Type2 visitRefExpr(RefExpr refExpr)
  {
    Type2 type = refExpr.accept(zExprChecker_);

    //get the type of this name
    ZName zName = refExpr.getZName();

    if (className() != null &&
        zName.getWord().equals(OzString.SELF) &&
        zName.getZStrokeList().size() == 0) {
      type  = getSelfType();
    }
    return type;
  }

  public Type2 visitClassUnionExpr(ClassUnionExpr classUnionExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr lExpr = classUnionExpr.getLeftExpr();
    Expr rExpr = classUnionExpr.getRightExpr();
    Type2 lType = lExpr.accept(this);
    Type2 rType = rExpr.accept(this);

    ClassType vlClassType = factory().createVariableClassType();
    PowerType vlPowerType = factory().createPowerType(vlClassType);
    ClassType vrClassType = factory().createVariableClassType();
    PowerType vrPowerType = factory().createPowerType(vrClassType);

    UResult lUnified = strongUnify(vlPowerType, lType);
    UResult rUnified = strongUnify(vrPowerType, rType);
    //if the left expr is not a class description, raise an error
    if (lUnified == FAIL) {
      Object [] params = {lExpr, lType};
      error(classUnionExpr, ErrorMessage.NON_CLASS_IN_CLASSUNIONEXPR, params);
    }

    //if the right expr is not a class description, raise an error
    if (rUnified == FAIL) {
      Object [] params = {rExpr,  rType};
      error(classUnionExpr, ErrorMessage.NON_CLASS_IN_CLASSUNIONEXPR, params);
    }

    //if we have class types, intersect the features of the two classes
    if (lUnified != FAIL && rUnified != FAIL &&
        vlPowerType.getType() instanceof ClassType &&
        vrPowerType.getType() instanceof ClassType) {
      ClassType lClassType = (ClassType) vlPowerType.getType();
      ClassType rClassType = (ClassType) vrPowerType.getType();
      //if both signatures are complete
      if (!instanceOf(lClassType, VariableClassType.class) &&
          !instanceOf(rClassType, VariableClassType.class)) {
        Type2 unioned = unionClasses(classUnionExpr, lClassType, rClassType);
        type = factory().createPowerType(unioned);
      }
    }

    //add the type annotation
    addTypeAnn(classUnionExpr, type);

    return type;
  }

  public Type2 visitPolyExpr(PolyExpr polyExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr expr = polyExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //if the left expr is not a class description, raise an error
    PowerType vPowerType = factory().createPowerType();
    //UResult unified = 
    		strongUnify(vPowerType, exprType);

    //if the expr is not a class type, raise an error
    if (!instanceOf(vPowerType.getType(), ClassRefType.class) &&
        !instanceOf(vPowerType.getType(), VariableType.class)) {
      Object [] params = {polyExpr, exprType};
      error(polyExpr, ErrorMessage.NON_REF_IN_POLYEXPR, params);
    }
    else if (vPowerType.getType() instanceof ClassRefType) {
      ClassRefType classRefType = (ClassRefType) vPowerType.getType();
      ClassRef cRef = classRefType.getThisClass();
      ClassRefList subClasses =
        factory().createClassRefList(factory().list(cRef));

      //find any subclasses
      List<NameSectTypeTriple> triples = sectTypeEnv().getTriple();
      for (NameSectTypeTriple triple : triples) {

        Type2 nextType = unwrapType(triple.getType());
        if (isPowerClassRefType(nextType)) {
          ClassRefType subClass =
            (ClassRefType) powerType(nextType).getType();

          if (contains(subClass.getSuperClass(), cRef)) {
            //the subclasses must have the same number of parameters as
            //the "top-level" class
            final int superSize = cRef.getType().size();
            final int subSize = subClass.getThisClass().getType().size();
            if (superSize != subSize) {
              Object [] params = {cRef.getName(), superSize,
                                  subClass.getThisClass().getName(),
                                  subSize, polyExpr};
              error(polyExpr,
                    ErrorMessage.PARAMETER_MISMATCH_IN_POLYEXPR, params);
            }

	    addDependency(subClass.getThisClass().getName());

            //all visible features must also be visible in the subclass
            List<NameTypePair> superAttrs = classRefType.getAttribute();
            List<NameTypePair> subAttrs = subClass.getAttribute();
            checkVisibility(classRefType, subClass, superAttrs,
                            subAttrs, polyExpr);

            List<NameTypePair> superState = classRefType.getState().getNameTypePair();
            List<NameTypePair> subState = subClass.getState().getNameTypePair();
            checkVisibility(classRefType, subClass, superState, subState, polyExpr);

            List<NameSignaturePair> superOps = classRefType.getOperation();
            List<NameSignaturePair> subOps = subClass.getOperation();
            checkOpVisibility(classRefType, subClass, superOps, subOps, polyExpr);

            ClassRef subCRef = factory().createClassRef();
            subCRef.setName(subClass.getThisClass().getName());
            subCRef.getType().addAll(cRef.getType());
            subCRef.getNewOldPair().addAll(cRef.getNewOldPair());
            if (!contains(subClasses, subCRef)) {
              subClasses.add(subCRef);
            }
          }
        }
      }
      ClassPolyType polyClass =
        factory().createClassPolyType(subClasses, classRefType.getState(),
                                      classRefType.getAttribute(),
                                      classRefType.getOperation(),
                                      classRefType.getThisClass());
      type = factory().createPowerType(polyClass);
    }

    //add the type annotation
    addTypeAnn(polyExpr, type);
    return type;
  }

  public Type2 visitContainmentExpr(ContainmentExpr containmentExpr)
  {
    Type2 type = factory().createUnknownType();

    Expr expr = containmentExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    //if the left expr is not a class description, raise an error
    ClassType vClassType = factory().createVariableClassType();
    PowerType vPowerType = factory().createPowerType(vClassType);
    UResult unified = strongUnify(vPowerType, exprType);

    //if the expr is not a class type, raise an error
    if (unified == FAIL) {
      Object [] params = {containmentExpr, exprType};
      error(containmentExpr, ErrorMessage.NON_CLASS_IN_CONTAINMENTEXPR, params);
    }
    else if (vPowerType.getType() instanceof ClassType) {
      type = exprType;
    }

    //add the type annotation
    addTypeAnn(containmentExpr, type);
    return type;
  }

  public Type2 visitPredExpr(PredExpr predExpr)
  {
    Type2 type = factory().createUnknownType();

    //visit the predicate
    Pred pred = predExpr.getPred();
    UResult solved = pred.accept(predChecker());

    if (solved == SUCC) {
      //create a boolean type (a power type containing an empty schema type)
      type = factory().createBoolType();
    }

    //add the type annotation
    addTypeAnn(predExpr, type);

    return type;
  }

  public Type2 visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    Type type = factory().createUnknownType();

    //get the type of the expression
    Expr expr = bindSelExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    if (instanceOf(exprType, VariableClassType.class) ||
        !instanceOf(exprType, VariableType.class)) {
      if (exprType instanceof SchemaType) {
        type = bindSelExpr.accept(zExprChecker_);
      }
      else if (exprType instanceof ClassType) {
        ClassType classType = (ClassType) exprType;
        ZName selectName = bindSelExpr.getZName();

        //if the selected name is "self", then simply type of this
        //is the same as the type of the expression
        if (selectName.getWord().equals(OzString.SELF) &&
            selectName.getZStrokeList().size() == 0) {
          type = classType;
        }
        else {
          //try to find the name in the state signature
          Signature signature = classType.getState();
          NameTypePair pair = findNameTypePair(selectName, signature);

          //if it is not found, try the attributes
          if (pair == null) {
            List<NameTypePair> pairs = classType.getAttribute();
            pair = findNameTypePair(selectName, pairs);
          }

          //if it is not in the state or attributes, raise an error
          if (pair == null) {
            Object [] params = {bindSelExpr};
            error(selectName, ErrorMessage.NON_EXISTENT_SELECTION, params);
          }
          //otherwise, the type is the type of the selection
          else {
            type = pair.getType();
          }
        }

        //if the feature exists, but it is not visible, raise an error
        if (!(type instanceof UnknownType)
            && !isVisible(selectName, exprType)) {
          Object [] params = {selectName, bindSelExpr};
          error(bindSelExpr, ErrorMessage.NON_VISIBLE_NAME_IN_SELEXPR, params);
        }
      }
      else {
        Object [] params = {bindSelExpr, exprType};
        error(bindSelExpr, ErrorMessage.NON_BINDING_IN_BINDSELEXPR, params);
      }
    }

    //try to resolve this type if it is unknown
    if (type instanceof Type2) {
      type = resolveUnknownType((Type2) type);
    }
    //if this is a reference to a generic declared inside a class,
    //being referenced outside of that class, the parameters must be
    //instantiated
    if (type instanceof GenericType) {
      GenericType gType = (GenericType) type;
      List<Type2> instantiations = factory().list();
      ParameterAnn pAnn =
        (ParameterAnn) bindSelExpr.getAnn(ParameterAnn.class);
      unificationEnv().enterScope();

      //add new vtypes for the (missing) parameters
      ZNameList paramNames = assertZNameList(gType.getNameList());
      for (Name paramName : paramNames) {
        //add a variable type corresponding to this name
        VariableType vType = factory().createVariableType();
        unificationEnv().addGenName(paramName, vType);
        instantiations.add(vType);
      }

      //instantiate the type
      type = (GenericType) instantiate(gType);

      if (pAnn != null) {
        removeAnn(bindSelExpr, pAnn);
      }
      pAnn = new ParameterAnn(instantiations);
      addAnn(bindSelExpr, pAnn);
      unificationEnv().exitScope();

      //add this for post-checking
      if (!containsObject(paraErrors(), bindSelExpr)) {
        addTermForPostChecking(bindSelExpr);
      }
    }

    //add the type annotation
    addTypeAnn(bindSelExpr, type);

    Type2 result = unwrapType(type);

    return result;
  }

  public Type2 visitRenameExpr(RenameExpr renameExpr)
  {
    Type2 type = factory().createUnknownType();

    //get the type of the expression
    Expr expr = renameExpr.getExpr();
    Type2 exprType = expr.accept(exprChecker());

    PowerType vPowerType = factory().createPowerType();
    UResult unified = strongUnify(vPowerType, exprType);

    if (unified == FAIL) {
      Object [] params = {renameExpr, exprType};
      error(renameExpr, ErrorMessage.NON_SCHEXPR_IN_RENAMEEXPR, params);
    }
    else if (!instanceOf(vPowerType.getType(), VariableType.class)) {
      if (vPowerType.getType() instanceof ClassRefType) {
        //add declname IDs to the new names
        addNameIDs(renameExpr.getZRenameList());

        //rename the class features
        ClassRefType classRefType = (ClassRefType) vPowerType.getType();
        String errorMessage =
          ErrorMessage.DUPLICATE_NAME_IN_RENAMEEXPR.toString();
        ClassRefType renameClassType =
          createRenameClassType(classRefType, renameExpr, errorMessage);
        type = factory().createPowerType(renameClassType);
      }
      else if (vPowerType.getType() instanceof SchemaType) {
        type = renameExpr.accept(zExprChecker_);
      }
      else {
        Object [] params = {renameExpr, exprType};
        error(renameExpr, ErrorMessage.NON_SCHEXPR_IN_RENAMEEXPR, params);

        if (vPowerType.getType() instanceof UnknownType) {
          UnknownType uType = (UnknownType) vPowerType.getType();
          if (uType.getZName() != null) {
            List<NewOldPair> newPairs =
              mergeRenamePairs(uType.getPairs(), renameExpr.getZRenameList());
            uType.getPairs().clear();
            uType.getPairs().addAll(newPairs);
          }
          type = uType;
        }
      }
    }

    //add the type annotation
    addTypeAnn(renameExpr, type);
    return type;
  }
}
