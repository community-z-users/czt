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
//import static net.sourceforge.czt.z.util.ZUtils.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.oz.util.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 *
 */
public class ParaChecker
  extends Checker<Signature>
  implements
    SchTextVisitor<Signature>,
    ClassParaVisitor<Signature>,
    StateVisitor<Signature>,
    InitialStateVisitor<Signature>,
    OperationVisitor<Signature>
{
  protected net.sourceforge.czt.typecheck.z.ParaChecker zParaChecker_;

  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zParaChecker_ =
      new net.sourceforge.czt.typecheck.z.ParaChecker(typeChecker);
  }

  public Signature visitTerm(Term term)
  {
    return term.accept(zParaChecker_);
  }

  public Signature visitSchText(SchText schText)
  {
    return schText.accept(zParaChecker_);
  }

  public Signature visitClassPara(ClassPara classPara)
  {
    //enter new variable scopes
    pending().enterScope();
    typeEnv().enterScope();

    //add the generic types to the type environment
    addGenParamTypes((ZNameList)classPara.getNameList());

    //set the class para
    setClassPara(classPara);

    //reset the primary variable list
    resetPrimary();

    //declare the info needed to create the class type
    //List<NameTypePair> attributes = factory().list();

    //create the class type from the information so far
    ClassRef thisClass = factory().createClassRef(className());
    for (ZName paramName : typeEnv().getParameters()) {
      Type2 gpType = factory().createGenParamType(paramName);
      thisClass.getType().add(gpType);
    }
    ClassRefList classes = 
      factory().createClassRefList(factory().listTerm(thisClass));
    ClassRefType classType =
      factory().createClassRefType(classes, factory().createSignature(),
                                   factory().<NameTypePair>list(),
                                   factory().<NameSignaturePair>list(),
                                   thisClass,
                                   factory().<ClassRef>list(), 
                                   null,
                                   factory().<Name>list());
    PowerType powerType = factory().createPowerType(classType);

    //add this class name and "self" to the pending typing environment
    ZName self = factory().createZDeclName(OzString.SELF);
    factory().addNameID(self);
    pending().add(self, addGenerics(classType));

    //visit each inherited class
    List<Expr> inheritedClass = classPara.getInheritedExpr();
    for (Expr iClass : inheritedClass) {
      visitInheritedClass(iClass);
    }

    //visit the attributes
    List<NameTypePair> attrDecls = factory().list();
    List<Para> attrs = classPara.getLocalDef();
    for (Para para : attrs) {
      Signature signature = para.accept(paraChecker());
      List<NameTypePair> newDecls = signature.getNameTypePair();
      checkForDuplicates(newDecls, null);
      typeEnv().add(newDecls);
      ZUtils.insert(attrDecls, newDecls);
    }
    
    //check that each attribute is unique within the class
    for (int i = 0; i < attrDecls.size(); i++) {
      ZName first = attrDecls.get(i).getZName();
      for (int j = i + 1; j < attrDecls.size(); j++) {
        ZName second = attrDecls.get(j).getZName();
        if (ZUtils.namesEqual(first, second) && true) {
          Object [] params = {second, className()};
          error(second, ErrorMessage.REDECLARED_NAME_IN_CLASSPARA, params);
        }
      }
    }

    //add the declarations to the class signature
    ZUtils.insert(classType.getAttribute(), attrDecls);

    //check for incompatible overriding
    checkForDuplicates(classType.getAttribute(), className(),
                       ErrorMessage.INCOMPATIBLE_OVERRIDING);

    //visit the state
    State state = classPara.getState();
    if (state != null) {
      //Signature signature = 
    		  state.accept(paraChecker());
      List<NameTypePair> decls = classType.getState().getNameTypePair();
      checkForDuplicates(decls,
                         className(),
                         ErrorMessage.INCOMPATIBLE_OVERRIDING);
    }

    //visit the initial predicate
    InitialState initialState = classPara.getInitialState();
    if (initialState != null) {
      //enter a new scope
      typeEnv().enterScope();

      //add the types in the state to the type env
      typeEnv().add(classType.getState().getNameTypePair());

      //visit the initial state
      initialState.accept(paraChecker());

      //exit the scope
      typeEnv().exitScope();
    }

    //add the "Init" variable to the state (to use for dereferencing)
    ZName initName = factory().createZDeclName(OzString.INITWORD);
    factory().addNameID(initName);
    NameTypePair existingInitPair = findNameTypePair(initName, classType.getState());
    if (existingInitPair == null) {
      Type2 boolType = factory().createBoolType();
      NameTypePair initPair = factory().createNameTypePair(initName, boolType);
      ZUtils.insert(classType.getState().getNameTypePair(), initPair);
    }

    //the list of operation names declared by this paragraph
    List<ZName> opNames = factory().list();

    //add implicit operations
    opExprChecker().addImplicitOps();

    //visit each operation
    List<Operation> operations = classPara.getOperation();
    for (Operation operation : operations) {
      //include the primed and unprimed state variables in a new scope
      enterOpScope(classType.getState());

      //visit the operation, and add its definition to the class info
      Signature opSignature = operation.accept(paraChecker());
      addOperation(operation.getZName(), opSignature, classType);

      //add the name of the operation
      opNames.add(operation.getZName());

      //add a unique ID to the operation name
      factory().addNameID(operation.getZName());

      //exit the scope
      typeEnv().exitScope();
    }

    //check the class type for duplicate declaration names
    checkClass(classType, className(), classPara.getVisibilityList(),
               ErrorMessage.REDECLARED_NAME_IN_CLASSPARA);
    checkForDuplicates(opNames);

    //add the visibility list to the signature now after the paragraph
    //has been completely visited
    classType.setVisibilityList(classPara.getVisibilityList());

    //add the primary variables list to the class type
    classType.getPrimary().addAll(primary());

    //create the signature of this paragraph
    NameTypePair cPair =
      factory().createNameTypePair(className(), addGenerics(powerType));
    Signature signature = factory().createSignature(factory().list(cPair));

    //exit the variable scopes
    pending().exitScope();
    typeEnv().exitScope();

    //add this as a signature annotation
    addSignatureAnn(classPara, signature);

    return signature;
  }

  public Signature visitState(State state)
  {
    List<NameTypePair> pairs = factory().list();

    //get the decls
    PrimaryDecl primaryDecl = state.getPrimaryDecl();
    SecondaryDecl secondaryDecl = state.getSecondaryDecl();

    //get the types in the declarations
    DeclList pDeclList = primaryDecl.getDeclList();
    DeclList sDeclList = secondaryDecl.getDeclList();
    List<NameTypePair> pPairs = pDeclList.accept(declChecker());
    List<NameTypePair> sPairs = sDeclList.accept(declChecker());
    ZUtils.insert(pairs, pPairs);
    ZUtils.insert(pairs, sPairs);

    //add the names in the primary decls to the list of primary
    //names
    for (NameTypePair pair : pPairs) {
      primary().add(pair.getZName());
    }

    //check the state for incompatible declarations
    checkForDuplicates(pairs, null);

    //add these pairs to the type env
    typeEnv().add(pairs);

    //add the pairs to the signature
    ClassType selfType = getSelfType();
    ZUtils.insert(selfType.getState().getNameTypePair(), pairs);

    //typecheck the predicate
    Pred pred = state.getPred();
    if (pred != null) {
      UResult solved = pred.accept(predChecker());
      //if there unsolved unifications, visit this again
      if (solved == PARTIAL) {
        pred.accept(predChecker());
      }
    }

    //create the signature
    Signature signature = factory().createSignature(pairs);

    //add the signature annotation
    addSignatureAnn(state, signature);

    return signature;
  }

  public Signature visitInitialState(InitialState initialState)
  {
    //enter a new scope
    typeEnv().enterScope();

    //visit the predicate
    Pred pred = initialState.getPred();
    UResult solved = pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (solved == PARTIAL) {
      pred.accept(predChecker());
    }

    //exit the variable scope
    typeEnv().exitScope();

    return null;
  }

  public Signature visitOperation(Operation operation)
  {
    ZName opName = operation.getZName();
    Signature signature = factory().createVariableSignature();

    //get the variables declared in the superclass's definition of
    //this operation
    ClassType selfType = getSelfType();
    NameSignaturePair superPair =
      findNameSigPair(opName, selfType.getOperation());
    if (superPair != null) {
      List<NameTypePair> pairs = superPair.getSignature().getNameTypePair();
      typeEnv().add(pairs);
    }

    SignatureAnn signatureAnn =
      (SignatureAnn) operation.getAnn(SignatureAnn.class);
    //if this has already been visited, return the signature
    if (signatureAnn != null) {
      signature = signatureAnn.getSignature();
    }
    //otherwise, calculate the signature
    else {
      NameSignaturePair temporaryPair =
        factory().createNameSignaturePair(opName, factory().createSignature());
      List<NameSignaturePair> opPairs = selfType.getOperation();
      boolean added = false;
      if (recursiveTypes()) {
        //before visiting, add this operation temporarily with an empty
        //signature to allow recursive definitions with itself
        NameSignaturePair existing = findNameSigPair(opName, opPairs);
        if (existing == null) {
          added = true;
          opPairs.add(temporaryPair);
        }
      }

      //visit the operation expression, and get the signature
      typeEnv().enterScope();
      OpExpr opExpr = operation.getOpExpr();
      signature = opExpr.accept(opExprChecker());
      typeEnv().exitScope();

      if (added) {
        //remove the the temporary pair again
        opPairs.remove(temporaryPair);
      }
    }

    return signature;
  }

  protected void visitInheritedClass(Expr expr)
  {
    //visit the expr
    Type2 exprType = expr.accept(exprChecker());

    PowerType vPowerType = factory().createPowerType();
    //UResult unified = 
    		strongUnify(vPowerType, exprType);

    //if the expr is not a class name reference, raise an error
    if (!instanceOf(vPowerType.getType(), ClassRefType.class) &&
        !instanceOf(vPowerType.getType(), VariableType.class)) {
      Object [] params = {expr};
      error(expr, ErrorMessage.NON_CLASS_INHERITED, params);
    }
    //otherwise, add this information to the current class signature
    else if (vPowerType.getType() instanceof ClassRefType) {
      ClassRefType classRefType = (ClassRefType) vPowerType.getType();
      ClassRefType current = getSelfType();

      //check whether the name of the inherited class is actually a
      //class paragraph.
      ClassRef classRef = classRefType.getThisClass();
      ZName superName = getZName(expr);
      if (!ZUtils.namesEqual(superName, classRef.getName())) {
        Object [] params = {expr};
        error(expr, ErrorMessage.NON_CLASS_INHERITED, params);
      }

      //add a dependency between this class and the super class
      addDependency(superName);

      //check that there is no cyclic inheritance
      List<ClassRef> currentSuperClasses = current.getSuperClass();
      List<ClassRef> superClasses = getSuperClasses(classRefType);
      for (ClassRef superClass : superClasses) {
        if (ZUtils.namesEqual(className(), superClass.getName())) {
          Object [] params = {className()};
          error(expr, ErrorMessage.CYCLIC_INHERITANCE, params);
        }

        //add the superclasses of the inherited class to the subclass's
        //superclass list
        if (!contains(currentSuperClasses, superClass)) {
          currentSuperClasses.add(superClass);
        }
      }

      //add the name of the superclass to current classes's superclass list
      ClassRef thisClass = classRefType.getThisClass();
      if (!contains(currentSuperClasses, thisClass)) {
        currentSuperClasses.add(thisClass);
      }

      //add the attributes to the subclass's signature and the type env
      inheritFeature(classRefType.getAttribute(), current.getAttribute(), expr);

      //add the decls to the subclass's signature and the type env
      inheritFeature(classRefType.getState().getNameTypePair(),
                     current.getState().getNameTypePair(),
                     expr);

      //add the primary variable names to the subclass's signature
      List<Name> primaryNames = classRefType.getPrimary();
      for (Name primaryName : primaryNames) {
        ZName zPrimaryName = ZUtils.assertZName(primaryName);
        current.getPrimary().add(zPrimaryName);
        primary().add(zPrimaryName);
      }

      //add the operations to the subclass's signature and the op env
      inheritOps(classRefType.getOperation(), current.getOperation(), expr);
    }
  }

  protected void enterOpScope(Signature signature)
  {
    //enter a scope
    typeEnv().enterScope();

    //for each pair in the state, add the primed and unprimed
    //variables into the environment
    List<NameTypePair> pairs = signature.getNameTypePair();
    for (NameTypePair pair : pairs) {
      ZName unprimed = pair.getZName();
      ZName primed = factory().createZName(unprimed, true);
      primed.getZStrokeList().add(factory().createNextStroke());
      typeEnv().add(unprimed, pair.getType());
      typeEnv().add(primed, pair.getType());
    }
  }
}
