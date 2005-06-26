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
      factory().createClassRefType(cSig, thisClass, list(), null);
    PowerType powerType = factory().createPowerType(classType);

    //add this class name and "self" to the pending typing environment
    DeclName self = factory().createDeclName(OzString.SELF, list(), null);
    pending().add(self, addGenerics(classType));

    //visit each inherited class
    List<Expr> inheritedClass = classPara.getInheritedClass();
    for (Expr iClass : inheritedClass) {
      visitInheritedClass(iClass, classType);

    }

    //visit the attributes
    List<NameTypePair> attrDecls = list();
    List<Para> attrs = classPara.getLocalDef();
    for (Para para : attrs) {
      Signature signature = (Signature) para.accept(paraChecker());
      List<NameTypePair> decls = list(cSig.getAttribute());
      List<NameTypePair> newDecls = signature.getNameTypePair();
      decls.addAll(newDecls);
      checkForDuplicates(decls, null, ErrorMessage.INCOMPATIBLE_OVERRIDING);
      typeEnv().add(newDecls);
      attrDecls.addAll(newDecls);
    }
    //add the declarations to the class signature
    cSig.getAttribute().addAll(attrDecls);

    //visit the state
    State state = classPara.getState();
    if (state != null) {
      Signature signature = (Signature) state.accept(paraChecker());
      List<NameTypePair> decls = list(cSig.getState().getNameTypePair());
      List<NameTypePair> newDecls = signature.getNameTypePair();
      decls.addAll(newDecls);
      checkForDuplicates(decls, null, ErrorMessage.INCOMPATIBLE_OVERRIDING);
    }

    //visit the initial predicate
    InitialState initialState = classPara.getInitialState();
    if (initialState != null) {
      //enter a new scope
      typeEnv().enterScope();

      //add the types in the state to the type env
      typeEnv().add(cSig.getState().getNameTypePair());

      List<NameTypePair> decls = cSig.getState().getNameTypePair();
      List<NameTypePair> newDecls = (List) initialState.accept(paraChecker());
      decls.addAll(newDecls);
      checkForDuplicates(decls, null, ErrorMessage.INCOMPATIBLE_OVERRIDING);

      //exit the scope
      typeEnv().exitScope();
    }

    //the list of operation names declared by this paragraph
    List<DeclName> opNames = list();

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
    checkForDuplicates(cSig, className(),
                       ErrorMessage.REDECLARED_NAME_IN_CLASSPARA);
    checkForDuplicates(opNames);

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

  public Object visitState(State state)
  {
    List<NameTypePair> pairs = list();

    //enter a new type env
    typeEnv().enterScope();

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
    UResult solved = (UResult) pred.accept(predChecker());

    //if the are unsolved unifications in this predicate,
    //visit it again
    if (solved == PARTIAL) {
      pred.accept(predChecker());
    }

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
    DeclName opName = operation.getName();
    Signature signature = factory().createVariableSignature();

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
      ClassSig cSig = getSelfSig();
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
      OpExpr opExpr = operation.getOpExpr();
      signature = (Signature) opExpr.accept(opExprChecker());

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

  protected Object visitInheritedClass(Expr expr, ClassRefType current)
  {
    //visit the expr
    Type2 exprType = (Type2) expr.accept(exprChecker());

    PowerType vPowerType = factory().createPowerType();
    UResult unified = strongUnify(vPowerType, exprType);

    //if the expr is not a class type, raise an error
    if (!instanceOf(vPowerType.getType(), ClassRefType.class) &&
        !instanceOf(vPowerType.getType(), VariableType.class)) {
      Object [] params = {expr, exprType};
      error(expr, ErrorMessage.NON_CLASS_INHERITED, params);
    }
    //otherwise, add this information to the current class signature
    else if (vPowerType.getType() instanceof ClassRefType) {
      ClassRefType classRefType = (ClassRefType) vPowerType.getType();
      ClassSig icSig = classRefType.getClassSig();
      ClassSig cSig = current.getClassSig();
      if (!instanceOf(icSig, VariableClassSig.class)) {
        //add the superclasses of the inherited class to the subclass's
        //superclass list
        current.getSuperClass().addAll(classRefType.getSuperClass());

        //add the name of the superclass to current's superclass list
        ClassRef thisClass = classRefType.getThisClass();
        current.getSuperClass().add(thisClass);

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

  protected void addStateVars(List<NameTypePair> pairs)
  {
    List<NameTypePair> already = getSelfType().getClassSig().getState().getNameTypePair();
    for (NameTypePair pair : pairs) {

      already.add(pair);
    }
  }
}
