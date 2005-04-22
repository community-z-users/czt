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
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.oz.util.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.typecheck.oz.impl.*;
import net.sourceforge.czt.typecheck.z.*;

/**
 *
 */
public class ParaChecker
  extends Checker
  implements
    ParaVisitor,
    SchTextVisitor,
    ClassParaVisitor,
    StateVisitor,
    InitialStateVisitor,
    OperationVisitor
{
  protected net.sourceforge.czt.typecheck.z.ParaChecker zParaChecker_;

  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zParaChecker_ =
      new net.sourceforge.czt.typecheck.z.ParaChecker(typeChecker);
  }

  public Object visitPara(Para para)
  {
    return para.accept(zParaChecker_);
  }

  public Object visitSchText(SchText schText)
  {
    return schText.accept(zParaChecker_);
  }

  public Object visitClassPara(ClassPara classPara)
  {
    //enter new variable scopes
    pending().enterScope();
    typeEnv().enterScope();

    //add the generic types to the type environment
    addGenParamTypes(classPara.getFormalParameters());

    //set the class name
    setClassName(classPara.getName());

    //reset the primary variable list
    resetPrimary();

    //declare the info needed to create the class type
    List<NameTypePair> attributes = list();

    //create the class type from the information so far
    ClassSig cSig = factory().createClassSig();
    cSig.setState(factory().createSignature());

    ClassRef thisClass = factory().createClassRef(className(), list(), list());
    cSig.getClasses().add(thisClass);
    ClassRefType classType =
      factory().createClassRefType(cSig, thisClass, list(), null);
    PowerType powerType = factory().createPowerType(classType);

    //add this class name and "self" to the typing environments
    DeclName self = factory().createDeclName(OzString.SELF, list(), null);
    pending().add(className(), addGenerics(powerType));
    typeEnv().add(self, addGenerics(classType));

    //visit each inherited class
    List<Expr> inheritedClass = classPara.getInheritedClass();
    for (Expr iClass : inheritedClass) {
      visitInheritedClass(iClass, classType);
    }

    //visit the attributes
    List<Para> attrs = classPara.getLocalDef();
    for (Para para : attrs) {
      Signature signature = (Signature) para.accept(paraChecker());
      List<NameTypePair> attrDecls = signature.getNameTypePair();
      cSig.getAttribute().addAll(attrDecls);
      typeEnv().add(attrDecls);
    }

    //visit the state
    State state = classPara.getState();
    if (state != null) {
      Signature signature = (Signature) state.accept(paraChecker());
      cSig.getState().getNameTypePair().addAll(signature.getNameTypePair());
    }

    //add the types in the state to the type env
    typeEnv().add(cSig.getState().getNameTypePair());

    //visit the initial predicate
    InitialState initialState = classPara.getInitialState();
    if (initialState != null) {
      List<NameTypePair> pairs = (List) initialState.accept(paraChecker());
      cSig.getState().getNameTypePair().addAll(pairs);
    }

    //visit each operation
    List<Operation> operations = classPara.getOperation();
    for (Operation operation : operations) {
      //include the primed and unprimed state variables in a new scope
      enterOpScope(cSig.getState());

      //visit the operation, and add its definition to the class info
      NameSignaturePair pair =
        (NameSignaturePair) operation.accept(paraChecker());
      cSig.getOperation().add(pair);

      //exit the scope
      typeEnv().exitScope();
    }

    //check the class signature for duplicate declaration names
    checkForDuplicates(cSig);

    //add the visibility list to the signature now after the paragraph
    //has been completely visited
    classType.setVisibilityList(classPara.getVisibilityList());

    //create the signature of this paragraph
    NameTypePair cPair =
      factory().createNameTypePair(className(), addGenerics(powerType));
    Signature signature = factory().createSignature(list(cPair));

    //exit the variable scopes
    pending().exitScope();
    typeEnv().exitScope();

    //add this as a signature annotation
    addSignatureAnn(classPara, signature);

    return signature;
  }

  /**
   * Returns a pair containing two lists of NameTypePairs. The first
   * element in the pair is the primary declarations, the second pair
   * is the second declarations.
   */
  public Object visitState(State state)
  {
    List<NameTypePair> pairs = list();

    //enter a new type env
    typeEnv().enterScope();

    //visit the decls
    List<PrimaryDecl> primaryDecls = state.getPrimaryDecl();
    List<SecondaryDecl> secondaryDecls = state.getSecondaryDecl();

    //get the types in the declarations
    for (PrimaryDecl decl : primaryDecls) {
      List<NameTypePair> pPairs = (List) decl.getDecl().accept(declChecker());
      pairs.addAll(pPairs);
      //add the names in the primary decls to the list of primary
      //names
      for (NameTypePair pair : pPairs) {
        primary().add(pair.getName());
      }
    }
    for (SecondaryDecl decl : secondaryDecls) {
      pairs.addAll((List) decl.getDecl().accept(declChecker()));
    }

    //add these pairs to the type env
    typeEnv().add(pairs);

    //typecheck the predicate
    //czt.todo: Uncomment this when corejava classes are regenerated
    /*
    Pred pred = state.getPred();
    if (pred != null) {
      UResult solved = (UResult) pred.accept(predChecker());
      //if there unsolved unifications, visit this again
      if (solved == PARTIAL) {
        pred.accept(predChecker());
      }
    }
    */

    //exit the type env
    typeEnv().exitScope();

    //create the signature
    Signature signature = factory().createSignature(pairs);

    //add the signature annotation
    addSignatureAnn(state, signature);

    return signature;
  }

  public Object visitInitialState(InitialState initialState)
  {
    List<NameTypePair> pairs = list();

    //visit the predicate
    Pred pred = initialState.getPred();
    pred.accept(predChecker());

    //the definition "Init : \bool" should be added to the state
    //signature. We return this declaration and it is added in visitClassPara
    DeclName initName =
      factory().createDeclName(OzString.INITWORD, list(), null);
    Type2 boolType = factory().createBoolType();
    NameTypePair pair = factory().createNameTypePair(initName, boolType);
    pairs.add(pair);
    return pairs;
  }

  public Object visitOperation(Operation operation)
  {
    OpExpr opExpr = operation.getOpExpr();
    Signature signature = (Signature) opExpr.accept(opExprChecker());
    NameSignaturePair pair =
      factory().createNameSignaturePair(operation.getName(), signature);
    return pair;
  }

  protected Object visitInheritedClass(Expr expr, ClassRefType superClass)
  {
    //visit the expr
    Type2 exprType = (Type2) expr.accept(exprChecker());

    ClassRefType vClassRefType = factory().createClassRefType();
    PowerType vPowerType = factory().createPowerType(vClassRefType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a class type, raise an error
    if (unified == FAIL) {
      Object [] params = {expr, exprType};
      error(expr, ErrorMessage.NON_CLASS_INHERITED, params);
    }
    //otherwise, add this information to the current class signature
    else {
      ClassSig icSig = vClassRefType.getClassSig();
      ClassSig cSig = superClass.getClassSig();
      if (!instanceOf(icSig, VariableClassSig.class)) {
        //add the superclasses of the inherited class to the subclass's
        //parent list
        cSig.getClasses().addAll(icSig.getClasses());

        //add the name of the superclass to the subclass's parent list
        ClassRef thisClass = vClassRefType.getThisClass();
        superClass.getSuperClass().add(thisClass);

        //add the attributes to the subclass's signature and the type env
        cSig.getAttribute().addAll(icSig.getAttribute());
        typeEnv().add(icSig.getAttribute());

        //add the decls to the subclass's signature and the type env
        List<NameTypePair> statePairs = icSig.getState().getNameTypePair();
        cSig.getState().getNameTypePair().addAll(statePairs);
        typeEnv().add(statePairs);

        //add the operations to the subclass's signature and the op env
        cSig.getOperation().addAll(icSig.getOperation());
      }
    }

    return null;
  }

  protected void enterOpScope(Signature signature)
  {
    //enter a scope
    typeEnv().enterScope();

    //for each pair in the state, add the primed and unprimed
    //variables into the environment
    List<NameTypePair> pairs = signature.getNameTypePair();
    for (NameTypePair pair : pairs) {
      DeclName unprimed = pair.getName();
      DeclName primed = factory().createDeclName(unprimed);
      primed.getStroke().add(factory().createNextStroke());
      typeEnv().add(unprimed, pair.getType());
      typeEnv().add(primed, pair.getType());
    }
  }
}
