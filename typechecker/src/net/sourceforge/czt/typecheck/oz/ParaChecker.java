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
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.typecheck.z.*;

/**
 *
 */
public class ParaChecker
  extends Checker
  implements ClassParaVisitor,
             StateVisitor,
             InitialStateVisitor,
             OperationVisitor
{
  protected TypeChecker typeChecker_;

  protected net.sourceforge.czt.typecheck.z.ParaChecker zParaChecker_;

  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    typeChecker_ = typeChecker;
    zParaChecker_ =
      new net.sourceforge.czt.typecheck.z.ParaChecker(typeChecker);
  }

  public Object visitTerm(Term term)
  {
    return term.accept(zParaChecker_);
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
    ClassSignature cSig = factory().createClassSignature();
    cSig.setClassName(className());
    cSig.setPrimaryDecl(factory().createSignature());
    cSig.setSecondaryDecl(factory().createSignature());
    ClassType classType = factory().createClassType(cSig);
    PowerType powerType = factory().createPowerType(classType);

    //add this class name and "self" to the typing environments
    DeclName self = factory().createDeclName(OzString.SELF, list(), null);
    pending().add(className(), addGenerics(powerType));
    typeEnv().add(self, addGenerics(classType));

    //visit each inherited class
    List<Expr> inheritedClass = classPara.getInheritedClass();
    for (Expr iClass : inheritedClass) {
      visitInheritedClass(iClass, cSig);
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
      cSig.getPrimaryDecl().getNameTypePair().addAll(signature.getNameTypePair());
    }

    //add the types in the state to the type env
    typeEnv().add(cSig.getPrimaryDecl().getNameTypePair());

    //visit the initial predicate
    InitialState initialState = classPara.getInitialState();
    if (initialState != null) {
      List<NameTypePair> pairs = (List) initialState.accept(paraChecker());
      cSig.getPrimaryDecl().getNameTypePair().addAll(pairs);
    }

    //visit each operation
    List<Operation> operations = classPara.getOperation();
    for (Operation operation : operations) {
      NameSignaturePair pair =
        (NameSignaturePair) operation.accept(paraChecker());
      cSig.getOperation().add(pair);
    }

    //check the class signature for duplicate declaration names
    checkForDuplicates(cSig);

    //add the visibility list to the signature now after the paragraph
    //has been completely visited
    cSig.getVisibility().addAll(classPara.getVisibility());

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
    List<Decl> primaryDecls = state.getPrimaryDecl();
    List<Decl> secondaryDecls = state.getSecondaryDecl();

    //get the types in the declarations
    for (Decl decl : primaryDecls) {
      List<NameTypePair> pPairs = (List) decl.accept(declChecker());
      pairs.addAll(pPairs);
      //add the names in the primary decls to the list of primary
      //names
      for (NameTypePair pair : pPairs) {
        primary().add(pair.getName());
      }
    }
    for (Decl decl : secondaryDecls) {
      pairs.addAll((List) decl.accept(declChecker()));
    }

    //add these pairs to the type env
    typeEnv().add(pairs);

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

  protected Object visitInheritedClass(Expr expr, ClassSignature cSig)
  {
    //visit the expr
    Type2 exprType = (Type2) expr.accept(exprChecker());

    ClassType vClassType = factory().createClassType();
    PowerType vPowerType = factory().createPowerType(vClassType);
    UResult unified = unify(vPowerType, exprType);

    //if the expr is not a class type, raise an error
    if (unified == FAIL) {
      Object [] params = {expr, exprType};
      error(expr, ErrorMessage.NON_CLASS_INHERITED, params);
    }
    //otherwise, add this information to the current class signature
    else {
      ClassSignature icSig = vClassType.getClassSignature();

      //add the superclasses of the inherited class to the subclass's
      //parent list
      cSig.getParentClass().addAll(icSig.getParentClass());

      //add the name of the superclass to the subclass's parent list
      RefName rcName = factory().createRefName(icSig.getClassName());
      cSig.getParentClass().add(rcName);

      //add the attributes to the subclass's signature and the type env
      cSig.getAttribute().addAll(icSig.getAttribute());
      typeEnv().add(icSig.getAttribute());

      //add the primary and second variables to the subclass's
      //signature and the type env
      List<NameTypePair> primPairs = icSig.getPrimaryDecl().getNameTypePair();
      List<NameTypePair> secPairs = icSig.getSecondaryDecl().getNameTypePair();
      cSig.getSecondaryDecl().getNameTypePair().addAll(secPairs);
      cSig.getPrimaryDecl().getNameTypePair().addAll(primPairs);
      typeEnv().add(primPairs);
      typeEnv().add(secPairs);

      //add the operations to the subclass's signature and the op env
      cSig.getOperation().addAll(icSig.getOperation());
    }

    return null;
  }
}
