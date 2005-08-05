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

  public Object visitTerm(Term term)
  {
    return term.accept(zParaChecker_);
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

    //set the class para
    setClassPara(classPara);

    //reset the primary variable list
    resetPrimary();

    //declare the info needed to create the class type
    List<NameTypePair> attributes = list();

    //create the class type from the information so far
    ClassSig cSig = factory().createClassSig();
    cSig.setState(factory().createSignature());

    ClassRef thisClass = factory().createClassRef(className(), list(), list());
    for (DeclName declName : typeEnv().getParameters()) {
      Type2 gpType = factory().createGenParamType(declName);
      thisClass.getType2().add(gpType);
    }
    cSig.getClasses().add(thisClass);
    ClassRefType classType =
      factory().createClassRefType(cSig, thisClass, list(), null, list());
    PowerType powerType = factory().createPowerType(classType);

    //add this class name and "self" to the pending typing environment
    DeclName self = factory().createDeclName(OzString.SELF, list(), null);
    pending().add(self, addGenerics(classType));

    //visit each inherited class
    List<Expr> inheritedClass = classPara.getInheritedClass();
    for (Expr iClass : inheritedClass) {
      visitInheritedClass(iClass);
    }

    //visit the attributes
    List<NameTypePair> attrDecls = list();
    List<Para> attrs = classPara.getLocalDef();
    for (Para para : attrs) {
      Signature signature = (Signature) para.accept(paraChecker());
      List<NameTypePair> newDecls = signature.getNameTypePair();
      typeEnv().add(newDecls);
      attrDecls.addAll(newDecls);
    }

    //check that each attribute is unique within the class
    for (int i = 0; i < attrDecls.size(); i++) {
      NameTypePair first = attrDecls.get(i);
      for (int j = i + 1; j < attrDecls.size(); j++) {
        NameTypePair second = attrDecls.get(j);
        if (first.getName().equals(second.getName())) {
          DeclName secondName = second.getName();
          Object [] params = {secondName, className()};
          error(secondName, ErrorMessage.REDECLARED_NAME_IN_CLASSPARA, params);
        }
      }
    }

    //add the declarations to the class signature
    cSig.getAttribute().addAll(attrDecls);

    //check for incompatible overriding
    checkForDuplicates(cSig.getAttribute(), null,
                       ErrorMessage.INCOMPATIBLE_OVERRIDING);

    //visit the state
    State state = classPara.getState();
    if (state != null) {
      Signature signature = (Signature) state.accept(paraChecker());
      List<NameTypePair> decls = cSig.getState().getNameTypePair();
      checkForDuplicates(decls, null, ErrorMessage.INCOMPATIBLE_OVERRIDING);
    }

    //visit the initial predicate
    InitialState initialState = classPara.getInitialState();
    if (initialState != null) {
      //enter a new scope
      typeEnv().enterScope();

      //add the types in the state to the type env
      typeEnv().add(cSig.getState().getNameTypePair());

      //visit the initial state
      initialState.accept(paraChecker());

      //exit the scope
      typeEnv().exitScope();
    }

    //add the "Init" variable to the state (to use for dereferencing)
    DeclName initName =
      factory().createDeclName(OzString.INITWORD, list(), null);
    Type2 boolType = factory().createBoolType();
    NameTypePair initPair = factory().createNameTypePair(initName, boolType);
    cSig.getState().getNameTypePair().add(initPair);
    checkForDuplicates(cSig.getState().getNameTypePair(), null);

    //the list of operation names declared by this paragraph
    List<DeclName> opNames = list();

    //add implicit operations
    opExprChecker().addImplicitOps();

    //visit each operation
    List<Operation> operations = classPara.getOperation();
    for (Operation operation : operations) {
      //include the primed and unprimed state variables in a new scope
      enterOpScope(cSig.getState());

      //visit the operation, and add its definition to the class info
      NameSignaturePair pair =
        (NameSignaturePair) operation.accept(paraChecker());
      addOperation(pair, cSig);

      //add the name of the operation
      opNames.add(pair.getName());

      //exit the scope
      typeEnv().exitScope();
    }

    //check the class signature for duplicate declaration names
    checkClassSig(cSig, className(), classPara.getVisibilityList(),
		  ErrorMessage.REDECLARED_NAME_IN_CLASSPARA);
    checkForDuplicates(opNames);

    //add the visibility list to the signature now after the paragraph
    //has been completely visited
    classType.setVisibilityList(classPara.getVisibilityList());

    //add the primary variables list to the class type
    classType.getPrimary().addAll(primary());

    //add the "self" variable to the state
    NameTypePair selfPair =
      factory().createNameTypePair(self, addGenerics(classType));
    cSig.getState().getNameTypePair().add(selfPair);

    //create the signature of this paragraph
    NameTypePair cPair =
      factory().createNameTypePair(className(), addGenerics(powerType));
    Signature signature = factory().createSignature(list(cPair));

    //add this class to the list of class names
    classNames().add(className());

    //exit the variable scopes
    pending().exitScope();
    typeEnv().exitScope();

    //add this as a signature annotation
    addSignatureAnn(classPara, signature);

    return signature;
  }

  public Object visitState(State state)
  {
    List<NameTypePair> pairs = list();

    //get the decls
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

    //check the state for incompatible declarations
    checkForDuplicates(pairs, null);

    //add these pairs to the type env
    typeEnv().add(pairs);

    //add the pairs to the signature
    ClassSig selfSig = getSelfSig();
    selfSig.getState().getNameTypePair().addAll(pairs);

    //typecheck the predicate
    Pred pred = state.getPred();
    if (pred != null) {
      UResult solved = (UResult) pred.accept(predChecker());
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

  public Object visitInitialState(InitialState initialState)
  {
    //enter a new scope
    typeEnv().enterScope();

    //visit the predicate
    Pred pred = initialState.getPred();
    UResult solved = (UResult) pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (solved == PARTIAL) {
      pred.accept(predChecker());
    }

    //exit the variable scope
    typeEnv().exitScope();

    return null;
  }

  public Object visitOperation(Operation operation)
  {
    DeclName opName = operation.getName();
    Signature signature = factory().createVariableSignature();

    //get the variables declared in the superclass's definition of
    //this operation
    ClassSig cSig = getSelfSig();
    NameSignaturePair superPair = findNameSigPair(opName, cSig.getOperation());
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
      List<NameSignaturePair> opPairs = cSig.getOperation();
      boolean added = false;
      if (useBeforeDecl()) {
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
      signature = (Signature) opExpr.accept(opExprChecker());
      typeEnv().exitScope();

      if (added) {
        //remove the the temporary pair again
        opPairs.remove(temporaryPair);
      }
    }

    //create the name/signature pair
    NameSignaturePair pair =
      factory().createNameSignaturePair(opName, signature);

    return pair;
  }

  protected Object visitInheritedClass(Expr expr)
  {
    //visit the expr
    Type2 exprType = (Type2) expr.accept(exprChecker());

    PowerType vPowerType = factory().createPowerType();
    UResult unified = strongUnify(vPowerType, exprType);    

    DeclName superName = getDeclName(expr);
    ClassRefType current = getSelfType();

    //if the expr is not a class name reference, raise an error
    if (!containsDeclName(classNames(), superName) &&
	(!useBeforeDecl() || sectTypeEnv().getSecondTime())) {
      Object [] params = {expr};
      error(expr, ErrorMessage.NON_CLASS_INHERITED, params);
    }
    //otherwise, add this information to the current class signature
    else if (vPowerType.getType() instanceof ClassRefType) {
      ClassRefType classRefType = (ClassRefType) vPowerType.getType();
      ClassSig icSig = classRefType.getClassSig();      
      ClassSig cSig = current.getClassSig();

      //check that there is no cyclic inheritance
      List<ClassRef> currentSuperClasses = current.getSuperClass();
      List<ClassRef> superClasses = getSuperClasses(classRefType);
      for (ClassRef superClass : superClasses) {
	RefName superClassName = superClass.getRefName();
	if (namesEqual(className(), superClassName)) {
	  Object [] params = {className()};
	  error(expr, ErrorMessage.CYCLIC_INHERITANCE, params);
	}

        //add the superclasses of the inherited class to the subclass's
        //superclass list
	if (!contains(currentSuperClasses, superClass)) {
	  currentSuperClasses.add(superClass);
	}
      }

      //add the name of the superclass to current's superclass list
      ClassRef thisClass = classRefType.getThisClass();
      current.getSuperClass().add(thisClass);
      
      if (!instanceOf(icSig, VariableClassSig.class)) {
        //add the attributes to the subclass's signature and the type env
        inheritFeature(icSig.getAttribute(), cSig.getAttribute(), expr);

        //add the decls to the subclass's signature and the type env
        inheritFeature(icSig.getState().getNameTypePair(),
                       cSig.getState().getNameTypePair(),
                       expr);

        //add the primary variable names to the subclass's signature
        List<DeclName> primary = classRefType.getPrimary();
        current.getPrimary().addAll(primary);
        primary().addAll(primary);

        //add the operations to the subclass's signature and the op env
        inheritOps(icSig.getOperation(), cSig.getOperation(), expr);
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

  protected void addStateVars(List<NameTypePair> pairs)
  {
    List<NameTypePair> already = getSelfType().getClassSig().getState().getNameTypePair();
    for (NameTypePair pair : pairs) {

      already.add(pair);
    }
  }
}
