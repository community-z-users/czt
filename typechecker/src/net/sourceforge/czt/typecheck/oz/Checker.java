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

import java.io.Writer;
import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.print.oz.PrintUtils;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.typecheck.z.util.TypeEnv;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.oz.util.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * A super class for the *Checker classes in the typechecker.
 */
abstract public class Checker
  extends net.sourceforge.czt.typecheck.z.Checker
{
  //the information required for the typechecker classes.
  protected TypeChecker typeChecker_;

  public Checker(TypeChecker typeChecker)
  {
    super(typeChecker);
    typeChecker_ = typeChecker;
  }

  //a Factory for creating Object-Z terms
  protected Factory factory()
  {
    return typeChecker_.ozFactory_;
  }

  //the operation expr checker
  protected Checker opExprChecker()
  {
    return typeChecker_.opExprChecker_;
  }

  //typing environment used in downcasting
  protected TypeEnv downcastEnv()
  {
    return typeChecker_.downcastEnv_;
  }

  //the current class name
  protected DeclName className()
  {
    return typeChecker_.classPara_.getName();
  }

  //the current class para
  protected ClassPara classPara()
  {
    return typeChecker_.classPara_;
  }

  //set the current class paragraph
  protected void setClassPara(ClassPara classPara)
  {
    typeChecker_.classPara_ = classPara;
  }

  //the lst of primary state variables in the current class
  protected List<DeclName> primary()
  {
    return typeChecker_.primary_;
  }

  //reset the list of primary variables in the current class to empty
  protected void resetPrimary()
  {
    typeChecker_.primary_.clear();
  }

  //typecheck a file using an instance of this typechecker
  protected List typecheck(TermA termA, SectionInfo sectInfo)
  {
    return TypeCheckUtils.typecheck(termA, sectInfo, markup());
  }

  protected void error(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(termA, error, params);
    error(termA, errorAnn);
  }

  protected void error(TermA termA,
                       net.sourceforge.czt.typecheck.z.ErrorMessage error,
                       Object [] params)
  {
    ErrorAnn errorAnn = this.errorAnn(termA, error.toString(), params);
    error(termA, errorAnn);
  }

  protected ErrorAnn errorAnn(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
                                     sectName(), nearestLocAnn(termA),
                                     markup());
    return errorAnn;
  }

  protected ErrorAnn errorAnn(TermA termA, String error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
                                     sectName(), nearestLocAnn(termA),
                                     markup());
    return errorAnn;
  }

  protected UResult strongUnify(Type2 typeA, Type2 typeB)
  {
    UnificationEnv unificationEnv = (UnificationEnv) unificationEnv();
    return unificationEnv.strongUnify(typeA, typeB);
  }

  protected UResult weakUnify(Type2 typeA, Type2 typeB)
  {
    UnificationEnv unificationEnv = (UnificationEnv) unificationEnv();
    return unificationEnv.weakUnify(typeA, typeB);
  }

  protected Type getType(RefName name)
  {
    Type type = downcastEnv().getType(name);
    if (type instanceof UnknownType ||
        (type instanceof UnknownType &&
         unknownType(type).getRefName() != null) ){
      type = super.getType(name);
    }
    else {
      System.err.println(name + " : " + type);
    }
    return type;
  }

  //go through a series of conjunctions to see if there is a downcast
  //so that downcasts can be performed either before or after the
  //predicate in which they are used.
  protected void traverseForDowncasts(Pred pred)
  {
    if (pred instanceof AndPred) {
      AndPred andPred = (AndPred) pred;
      Pred leftPred = andPred.getLeftPred();
      Pred rightPred = andPred.getRightPred();
      traverseForDowncasts(leftPred);
      traverseForDowncasts(rightPred);
    }
    else if  (pred instanceof MemPred) {
      MemPred memPred = (MemPred) pred;
      boolean mixfix = memPred.getMixfix().booleanValue();
      if (!mixfix) {
        memPred.accept(predChecker());
      }
    }
  }

  //go through a series of conj op exprs to see if there is a downcast
  //so that downcasts can be performed either before or after the
  //predicate in which they are used.
  protected void traverseForDowncasts(OpExpr opExpr)
  {
    if (opExpr instanceof ConjOpExpr) {
      ConjOpExpr conjOpExpr = (ConjOpExpr) opExpr;
      OpExpr leftOpExpr = conjOpExpr.getLeftOpExpr();
      OpExpr rightOpExpr = conjOpExpr.getRightOpExpr();
      traverseForDowncasts(leftOpExpr);
      traverseForDowncasts(rightOpExpr);
    }
    else if (opExpr instanceof AnonOpExpr) {
      AnonOpExpr anonOpExpr = (AnonOpExpr) opExpr;
      OpText opText = anonOpExpr.getOpText();
      SchText schText = opText.getSchText();

      //the list of Names declared in this schema text
      List<NameTypePair> pairs = list();

      //get and visit the list of declarations
      List<Decl> decls = schText.getDecl();
      for (Decl decl : decls) {
        pairs.addAll((List<NameTypePair>) decl.accept(declChecker()));
      }

      downcastEnv().enterScope();
      for (NameTypePair pair : pairs) {
        downcastEnv().add(pair.getName(), pair.getType());
      }
      traverseForDowncasts(schText.getPred());
      downcastEnv().exitScope();
    }
  }

  protected void inheritFeature(List<NameTypePair> source,
                                List<NameTypePair> target,
                                Expr expr)
  {
    for (NameTypePair pair : source) {
      DeclName sourceName = pair.getName();
      NameTypePair existing = findNameTypePair(sourceName, target);
      if (existing != null) {
        Type2 sourceType = unwrapType(pair.getType());
        Type2 existingType = unwrapType(existing.getType());
        UResult unified = unify(sourceType, existingType);
        if (unified == FAIL) {
          Object [] params = {sourceName, sourceType, existingType};
          error(expr, ErrorMessage.INCOMPATIBLE_INHERIT, params);
        }
      }
      else {
        typeEnv().add(pair);
        target.add(pair);
      }
    }
  }

  protected void inheritOps(List<NameSignaturePair> source,
                            List<NameSignaturePair> target,
                            Expr expr)
  {
    for (NameSignaturePair pair : source) {
      DeclName sourceName = pair.getName();
      NameSignaturePair existing = findNameSigPair(sourceName, target);
      if (existing != null) {
        Signature sourceSignature = pair.getSignature();
        Signature existingSignature = existing.getSignature();
        UResult unified = unify(sourceSignature, existingSignature);
        if (unified == FAIL) {
          Object [] params = {sourceName, sourceSignature, existingSignature};
          error(expr, ErrorMessage.INCOMPATIBLE_OP_INHERIT, params);
        }
      }
      else {
        target.add(pair);
      }
    }
  }

  //get the type of "self"
  protected ClassRefType getSelfType()
  {
    RefName refName = factory().createRefName(OzString.SELF, list(), null);
    RefExpr refExpr = factory().createRefExpr(refName, list(), Boolean.FALSE);
    Type2 selfType = (Type2) refExpr.accept(exprChecker());
    assert selfType instanceof ClassRefType;
    ClassRefType result = (ClassRefType) selfType;
    return result;
  }

  //get the class signature of "self"
  protected ClassSig getSelfSig()
  {
    ClassType classType = getSelfType();
    ClassSig result = classType.getClassSig();
    return result;
  }

  //returns true if and only if the expressions is a reference to the
  //variable "self"
  protected boolean isSelfExpr(Expr expr)
  {
    boolean result = false;
    if (expr instanceof RefExpr) {
      RefExpr refExpr = (RefExpr) expr;
      RefName refName = refExpr.getRefName();
      result = refName.getWord().equals(OzString.SELF) &&
        refName.getStroke().size() == 0;
    }
    return result;
  }

  //take the intersection of 2 signatures
  protected Signature intersect(Signature sigA, Signature sigB)
  {
    Signature signature = factory().createSignature();
    List<NameTypePair> pairsA = sigA.getNameTypePair();
    List<NameTypePair> pairsB = sigB.getNameTypePair();
    for (NameTypePair pairA : pairsA) {
      NameTypePair pairB = findNameTypePair(pairA.getName(), sigB);
      if (pairB != null) {
        signature.getNameTypePair().add(pairA);
        signature.getNameTypePair().add(pairB);
      }
    }
    return signature;
  }

  //merge two class signatures and place result in newSig
  protected void merge(ClassSig newSig, ClassSig oldSig, TermA termA)
  {
    //merge the attributes
    List<NameTypePair> attrDecls = newSig.getAttribute();
    attrDecls.addAll(oldSig.getAttribute());
    checkForDuplicates(attrDecls, termA, ErrorMessage.INCOMPATIBLE_OVERRIDING);

    //merge the state signature
    List<NameTypePair> stateDecls = newSig.getState().getNameTypePair();
    stateDecls.addAll(oldSig.getState().getNameTypePair());
    checkForDuplicates(stateDecls, termA, ErrorMessage.INCOMPATIBLE_OVERRIDING);

    //merge the operations
    List<NameSignaturePair> newPairs = newSig.getOperation();
    for (NameSignaturePair newPair : newPairs) {
      DeclName declName = newPair.getName();
      NameSignaturePair oldPair = findNameSigPair(declName, oldSig.getOperation());
      if (oldPair == null) {
        newSig.getOperation().add(newPair);
      }
      else {
        UResult unified = unify(oldPair.getSignature(), newPair.getSignature());
        if (unified == FAIL) {
          Object [] params = {declName, termA};
          error(declName, ErrorMessage.INCOMPATIBLE_OVERRIDING, params);
        }
      }
    }
  }

  protected void addOperation(NameSignaturePair op, ClassSig cSig)
  {
    List<NameSignaturePair> ops = cSig.getOperation();
    DeclName opName = op.getName();
    NameSignaturePair existing = findOperation(opName, cSig);
    if (existing != null) {
      List<NameTypePair> pairs = list(op.getSignature().getNameTypePair());
      pairs.addAll(existing.getSignature().getNameTypePair());
      checkForDuplicates(pairs, opName, ErrorMessage.INCOMPATIBLE_OP_OVERRIDING);
      Signature newSig = factory().createSignature(pairs);
      NameSignaturePair newPair = factory().createNameSignaturePair(opName, newSig);
      cSig.getOperation().remove(existing);
      cSig.getOperation().add(newPair);
    }
    else {
      cSig.getOperation().add(op);
    }
  }

  protected void checkForDuplicates(List<NameTypePair> pairs,
                                    TermA termA,
                                    ErrorMessage error)
  {
    checkForDuplicates(pairs, termA, error.toString());
  }

  //check for duplicate names a class paragraph
  protected void checkForDuplicates(List<DeclName> declNames)
  {
    for (int i = 0; i < declNames.size(); i++) {
      DeclName first = declNames.get(i);
      for (int j = i + 1; j < declNames.size(); j++) {
        DeclName second = declNames.get(j);
        if (first.equals(second)) {
          Object [] params = {second, className()};
          error(second, ErrorMessage.REDECLARED_NAME_IN_CLASSPARA, params);
        }
      }
    }
  }

  //check for duplicates in a class paragraph
  protected void checkForDuplicates(ClassSig cSig, TermA termA,
                                    ErrorMessage errorMessage)
  {
    List<DeclName> decls = list(className());

    //collect the names
    List<NameTypePair> attrDecls = cSig.getAttribute();
    for (NameTypePair pair : attrDecls) {
      decls.add(pair.getName());
    }
    Signature stateSig = cSig.getState();
    List<NameTypePair> stateDecls = stateSig.getNameTypePair();
    for (NameTypePair pair : stateDecls) {
      decls.add(pair.getName());
    }
    List<NameSignaturePair> opDecls = cSig.getOperation();
    for (NameSignaturePair pair : opDecls) {
      decls.add(pair.getName());
    }

    //check for duplicate names
    for (int i = 0; i < decls.size(); i++) {
      DeclName first = decls.get(i);
      for (int j = i + 1; j < decls.size(); j++) {
        DeclName second = decls.get(j);
        if (first.equals(second)) {
          Object [] params = {first, termA};
          error(first, errorMessage, params);
        }
      }
    }
  }

  protected void checkVisibility(ClassRefType superClass,
                                 ClassRefType subClass,
                                 List<NameTypePair> superPairs,
                                 List<NameTypePair> subPairs,
                                 PolyExpr polyExpr)
  {
    for (NameTypePair superPair : superPairs) {
      RefName superName = factory().createRefName(superPair.getName());
      if (isVisible(superName, superClass)) {
        NameTypePair subPair = findNameTypePair(superName, subPairs);
        if (subPair == null || !isVisible(superName, subClass)) {
          Object [] params = {subClass.getThisClass().getRefName(),
                              superName,
                              superClass.getThisClass().getRefName(),
                              polyExpr};

          error(polyExpr,
                ErrorMessage.NON_VISIBLE_FEATURE_IN_POLYEXPR, params);
        }
      }
    }
  }

  protected void checkOpVisibility(ClassRefType superClass,
                                   ClassRefType subClass,
                                   List<NameSignaturePair> superPairs,
                                   List<NameSignaturePair> subPairs,
                                   PolyExpr polyExpr)
  {
    for (NameSignaturePair superPair : superPairs) {
      RefName superName = factory().createRefName(superPair.getName());
      if (isVisible(superName, superClass)) {
        NameSignaturePair subPair = findNameSigPair(superName, subPairs);
        if (subPair == null || !isVisible(superName, subClass)) {
          Object [] params = {subClass.getThisClass().getRefName(),
                              superName,
                              superClass.getThisClass().getRefName(),
                              polyExpr};

          error(polyExpr,
                ErrorMessage.NON_VISIBLE_FEATURE_IN_POLYEXPR, params);
        }
        else if (subPair != null) {
          Signature superSig = superPair.getSignature();
          Signature subSig = subPair.getSignature();
          UResult unified = unify(superSig, subSig);
          if (unified == FAIL) {
            Object [] params = {superName, polyExpr,
                                subClass.getThisClass().getRefName(),
                                superClass.getThisClass().getRefName(),
                                superSig, subSig};

            error(polyExpr,
                  ErrorMessage.INCOMPATIBLE_OP_IN_POLYEXPR, params);
          }
        }

      }
    }
  }

  protected Signature createPloSig(Signature lSig, Signature rSig,
                                   TermA termA, String errorMessage)
  {
    //b3 and b4 correspond to the variable names "\Beta_3" and
    //"\Beta_4" in the standard for piping expr
    List<NameTypePair> b3Pairs = list(lSig.getNameTypePair());
    List<NameTypePair> b4Pairs = list(rSig.getNameTypePair());
    List<NameTypePair> rPairs = rSig.getNameTypePair();

    for (NameTypePair rPair : rPairs) {
      DeclName rName = (DeclName) rPair.getName();
      List<Stroke> strokes = list(rName.getStroke());
      int size = strokes.size();
      if (size > 0 && strokes.get(size - 1) instanceof InStroke) {
        OutStroke out = factory().createOutStroke();
        strokes.set(size - 1, out);
        DeclName sName = factory().createDeclName(rName.getWord(),
                                                  strokes, null);
        NameTypePair foundPair = findNameTypePair(sName, lSig);
        if (foundPair != null) {
          Type2 fType = unwrapType(foundPair.getType());
          Type2 rType = unwrapType(rPair.getType());
          UResult unified = unify(fType, rType);
          if (unified == FAIL) {
            Object [] params = {termA, sName, fType, rName, rType};
            error(termA, errorMessage, params);
          }
          b4Pairs.remove(rPair);
        }
      }
    }
    //create the signature
    b3Pairs.addAll(b4Pairs);
    Signature result = factory().createSignature(b3Pairs);
    return result;
  }

  //rename the declarations
  protected List<NameSignaturePair> renameOps(List<NameSignaturePair> ops,
                                              List<NameNamePair> namePairs)
  {
    List<NameSignaturePair> newPairs = list();
    for (NameSignaturePair pair : ops) {
      NameNamePair namePair = findNameNamePair(pair.getName(), namePairs);
      if (namePair != null) {
        DeclName newName = namePair.getNewName();
        NameSignaturePair newPair =
          factory().createNameSignaturePair(newName, pair.getSignature());
        newPairs.add(newPair);
      }
      else {
        newPairs.add(pair);
      }
    }
    return newPairs;
  }

  protected ClassSig createRenameClassSig(ClassSig cSig,
                                          RenameExpr renameExpr,
                                          String errorMessage)
  {
    List<NameNamePair> namePairs = renameExpr.getNameNamePair();
    checkForDuplicateRenames(namePairs, renameExpr,  errorMessage);

    List<NameTypePair> attrs = cSig.getAttribute();
    Signature attrSig = factory().createSignature(attrs);
    Signature newAttrSig = rename(attrSig, namePairs);
    List<NameTypePair> newAttrs = newAttrSig.getNameTypePair();

    Signature state = cSig.getState();
    Signature newState = rename(state, namePairs);

    List<NameSignaturePair> ops = cSig.getOperation();
    List<NameSignaturePair> newOps = renameOps(ops, namePairs);

    ClassSig result = factory().createClassSig(cSig.getClasses(),
                                               newState, newAttrs, newOps);
    checkForDuplicates(result, renameExpr,
                       ErrorMessage.REDECLARED_NAME_IN_RENAMEEXPR);
    return result;
  }

  protected Type2 instantiate(Type2 type, Type rootType)
  {
    Type2 result = factory().createUnknownType();
    //if this is a class type, instantiate it
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      ClassSig cSig = classType.getClassSig();

      ClassSig newCSig = null;
      if (!(cSig instanceof VariableClassSig)) {

        //instantiate the state
        Signature state = cSig.getState();
        Signature newState = null;
        if (state != null) {
          newState = instantiate(state, rootType);
        }

        //instantiate the attributes
        List<NameTypePair> attrs = cSig.getAttribute();
        List<NameTypePair> newAttrs = instantiatePairs(attrs, rootType);

        //instantiate the operations
        List<NameSignaturePair> ops = cSig.getOperation();
        List<NameSignaturePair> newOps = list();
        for (NameSignaturePair pair : ops) {
          Signature signature = instantiate(pair.getSignature(), rootType);
          NameSignaturePair newPair =
            factory().createNameSignaturePair(pair.getName(), signature);
          newOps.add(newPair);
        }

        //instaniate the class references
        List<ClassRef> classRefs = cSig.getClasses();
        List<ClassRef> newClassRefs = list();
        for (ClassRef classRef : classRefs) {
          List<Type2> types = instantiateTypes(classRef.getType2(), rootType);
          ClassRef newClassRef =
            factory().createClassRef(classRef.getRefName(), types, list());
          newClassRefs.add(newClassRef);
        }
        newCSig =
          factory().createClassSig(newClassRefs, newState, newAttrs, newOps);
      }

      if (type instanceof ClassRefType) {
        ClassRefType classRefType = (ClassRefType) type;
        ClassRef classRef = instantiate(classRefType.getThisClass(), rootType);
        result = factory().createClassRefType(newCSig, classRef,
                                              classRefType.getSuperClass(),
                                              classRefType.getVisibilityList(),
                                              classRefType.getPrimary());
      }
      else if (type instanceof ClassPolyType) {
        ClassPolyType classPolyType = (ClassPolyType) type;
        ClassRef classRef = instantiate(classPolyType.getRootClass(), rootType);
        result = factory().createClassPolyType(newCSig, classRef);
      }
      else {
        ClassUnionType classUnionType = (ClassUnionType) type;
        result = factory().createClassUnionType(newCSig);
      }
    }
    //if not a class type, use the Z typechecker's instantiate method
    else {
      result = super.instantiate(type, rootType);
    }
    return result;
  }

  protected ClassRef instantiate(ClassRef classRef, Type rootType)
  {
    List<Type2> types = instantiateTypes(classRef.getType2(), rootType);
    ClassRef result =
      factory().createClassRef(classRef.getRefName(), types, list());
    return result;
  }

  protected List<ClassRef> getClasses(Type2 type)
  {
    List<ClassRef> classes = list();
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      classes = getClasses(classType.getClassSig());
    }
    return classes;
  }

  //get the classes that make up the parents of the class name.
  protected List<ClassRef> getClasses(ClassSig cSig)
  {
    List<ClassRef> classes = cSig.getClasses();
    return classes;
  }

  //find an attribute in a class signature
  protected NameTypePair findAttribute(DeclName declName, ClassSig cSig)
  {
    NameTypePair result = findNameTypePair(declName, cSig.getAttribute());
    return result;
  }

  //find a state variable in a class signature
  protected NameTypePair findStateDecl(DeclName declName, ClassSig cSig)
  {
    List<NameTypePair> decls = cSig.getState().getNameTypePair();
    NameTypePair result = findNameTypePair(declName, decls);
    return result;
  }

  //find a NameSignaturePair in a class signature
  protected NameSignaturePair findOperation(DeclName declName, ClassSig cSig)
  {
    NameSignaturePair result = findNameSigPair(declName, cSig.getOperation());
    return result;
  }

  protected NameSignaturePair findOperation(RefName refName, ClassSig cSig)
  {
    DeclName declName = factory().createDeclName(refName);
    NameSignaturePair result = findOperation(declName, cSig);
    return result;
  }

  protected NameSignaturePair findNameSigPair(RefName refName,
                                              List<NameSignaturePair> pairs)
  {
    DeclName declName = factory().createDeclName(refName);
    NameSignaturePair result = findNameSigPair(declName, pairs);
    return result;
  }

  protected NameSignaturePair findNameSigPair(DeclName declName,
                                              List<NameSignaturePair> pairs)
  {
    NameSignaturePair result = null;
    //find the pair that has this name
    for(NameSignaturePair pair : pairs) {
      if (declName.equals(pair.getName())) {
        result = pair;
        break;
      }
    }
    return result;
  }

  protected ClassRef findRef(RefName refName, List<ClassRef> classRefs)
  {
    ClassRef result = null;
    for (ClassRef classRef : classRefs) {
      if (refName.equals(classRef.getRefName())) {
        result = classRef;
      }
    }
    return result;
  }

  protected Type2 resolveUnknownType(Type2 type)
  {
    Type2 result = type;
    if (sectTypeEnv().getSecondTime() && type instanceof UnknownType) {
      UnknownType uType = (UnknownType) type;
      Type2 resolved = super.resolveUnknownType(uType);
      result = renameClassType(resolved, uType.getPairs());
    }
    return result;
  }

  protected Type2 renameClassType(Type2 type, List<NameNamePair> pairs)
  {
    Type2 result = type;
    if (type instanceof ClassType && pairs.size() > 0) {
      ClassType classType = (ClassType) type;
      ClassSig cSig = classType.getClassSig();
      List<NameTypePair> attrs = cSig.getAttribute();
      Signature attrSig = factory().createSignature(attrs);
      Signature newAttrSig = rename(attrSig, pairs);
      List<NameTypePair> newAttrs = newAttrSig.getNameTypePair();

      Signature state = cSig.getState();
      Signature newState = rename(state, pairs);

      List<NameSignaturePair> ops = cSig.getOperation();
      List<NameSignaturePair> newOps = renameOps(ops, pairs);

      ClassSig newCSig = factory().createClassSig(cSig.getClasses(),
                                                  newState, newAttrs, newOps);
      result = (Type2) classType.create(result.getChildren());
      ((ClassType) result).setClassSig(newCSig);
    }
    return result;
  }

  protected Type2 lookupClass(ClassRef classRef)
  {
    Type2 result = factory().createUnknownType();
    Type refType = getType(classRef.getRefName());
    if (refType instanceof GenericType) {
      List<DeclName> names = genericType(refType).getName();
      List<Type2> types = classRef.getType2();
      if (names.size() == types.size()) {
        unificationEnv().enterScope();
        for (int i = 0; i < names.size(); i++) {
          unificationEnv().addGenName(names.get(i), types.get(i));
        }
        Type newType = instantiate(refType);
        refType = newType;
        unificationEnv().exitScope();
      }
    }

    if (unwrapType(refType) instanceof PowerType) {
      PowerType powerType = (PowerType) unwrapType(refType);
      result = renameClassType(powerType.getType(), classRef.getNameNamePair());
    }
    return result;
  }

  protected Type2 unionClasses(ClassUnionExpr classUnionExpr,
                               Type2 lType, Type2 rType)
  {
    Type2 result = factory().createUnknownType();
    if (lType instanceof ClassType && rType instanceof ClassType) {
      ClassType lClassType = (ClassType) lType;
      ClassType rClassType = (ClassType) rType;
      ClassSig lcSig = lClassType.getClassSig();
      ClassSig rcSig = rClassType.getClassSig();

      List<ClassRef> classes = list();
      Signature state = factory().createSignature();
      List<NameTypePair> attrs = list();
      List<NameSignaturePair> ops = list();

      //check that the features are compatible, and find common elements
      List<NameTypePair> lsPairs = lcSig.getState().getNameTypePair();
      List<NameTypePair> rsPairs = rcSig.getState().getNameTypePair();
      for (NameTypePair lPair : lsPairs) {
        NameTypePair rPair = findNameTypePair(lPair.getName(), rsPairs);
        if (rPair != null) {
          state.getNameTypePair().add(lPair);
          state.getNameTypePair().add(rPair);
        }
      }
      //check compatibility
      if (classUnionExpr != null) {
        checkForDuplicates(state.getNameTypePair(), classUnionExpr,
                           ErrorMessage.INCOMPATIBLE_FEATURE_IN_CLASSUNIONEXPR);
      }

      List<NameTypePair> laPairs = lcSig.getAttribute();
      List<NameTypePair> raPairs = rcSig.getAttribute();
      for (NameTypePair lPair : laPairs) {
        NameTypePair rPair = findNameTypePair(lPair.getName(), raPairs);
        if (rPair != null) {
          attrs.add(lPair);
          attrs.add(rPair);
        }
      }
      //check compatibility
      if (classUnionExpr != null) {
        checkForDuplicates(attrs, classUnionExpr,
                           ErrorMessage.INCOMPATIBLE_FEATURE_IN_CLASSUNIONEXPR);
      }

      List<NameSignaturePair> loPairs = lcSig.getOperation();
      List<NameSignaturePair> roPairs = rcSig.getOperation();
      for (NameSignaturePair lPair : loPairs) {
        DeclName lName = lPair.getName();
        NameSignaturePair rPair = findOperation(lName, rcSig);
        if (rPair != null) {
          Signature lSig = lPair.getSignature();
          Signature rSig = rPair.getSignature();
          UResult unified = unify(lSig, rSig);
          if (unified == FAIL && classUnionExpr != null) {
            Object [] params = {lName, classUnionExpr, lSig, rSig};
            error(lName, ErrorMessage.INCOMPATIBLE_OP_IN_CLASSUNIONEXPR, params);
          }
          else {
            ops.add(lPair);
          }
        }
      }

      //add the class references
      classes.addAll(lcSig.getClasses());
      classes.addAll(rcSig.getClasses());
      ClassSig cSig = factory().createClassSig(classes, state, attrs, ops);
      result = factory().createClassUnionType(cSig);
    }
    return result;
  }

  protected Type2 resolveClassType(Type2 type)
  {
    Type2 result = type;
    if (type instanceof ClassUnionType && sectTypeEnv().getSecondTime()) {
      ClassUnionType cuType = (ClassUnionType) type;
      ClassSig cSig = cuType.getClassSig();
      List<ClassRef> classes = cSig.getClasses();

      assert classes.size() > 1;
      Type2 firstType = lookupClass(classes.get(0));
      Type2 secondType = lookupClass(classes.get(1));
      Type2 unioned = unionClasses(null, firstType, secondType);
      for (int i = 2; i < classes.size(); i++) {
        Type2 nextType = lookupClass(classes.get(0));
        unioned = unionClasses(null, unioned, nextType);
      }
      result = unioned;
    }
    else if (type instanceof ClassType && sectTypeEnv().getSecondTime()) {
      ClassRef classRef = null;
      if (type instanceof ClassRefType) {
        ClassRefType classRefType = (ClassRefType) type;
        classRef = classRefType.getThisClass();
      }
      else if (type instanceof ClassPolyType) {
        ClassPolyType classPolyType = (ClassPolyType) type;
        classRef = classPolyType.getRootClass();
      }
      result = lookupClass(classRef);
    }
    return result;
  }

  protected ClassRef rename(ClassRef classRef, RenameExpr renameExpr)
  {
    List<NameNamePair> cfPairs = classRef.getNameNamePair();
    List<NameNamePair> rnPairs = renameExpr.getNameNamePair();
    List<NameNamePair> newPairs = list();
    for (NameNamePair rnPair :rnPairs) {
      NameNamePair cfPair = findNameNamePair(rnPair.getNewName(), cfPairs);
      if (cfPair == null) {
        newPairs.add(rnPair);
      }
      else {
        NameNamePair newPair =
          factory().createNameNamePair(cfPair.getOldName(), rnPair.getNewName());
      }
    }
    ClassRef result = factory().createClassRef(classRef.getRefName(),
                                               classRef.getType2(),
                                               newPairs);
    return result;
  }

  protected CarrierSet getCarrierSet()
  {
    return new net.sourceforge.czt.typecheck.oz.util.CarrierSet(true);
  }

  protected void print(Term term,
                       Writer writer,
                       SectionInfo sectInfo,
                       String sectName,
                       Markup markup)
  {
    PrintUtils.print(term, writer, sectInfo, sectName, markup());
  }

  public String toString(Type type)
  {
    String result = new String();
    if (unwrapType(type) instanceof PowerType &&
        powerType(unwrapType(type)).getType() instanceof ClassRefType) {
      net.sourceforge.czt.oz.ast.ClassRefType ctype =
        (ClassRefType) powerType(unwrapType(type)).getType();
      result = "P " + classRefTypeToString(ctype);
    }
    else if (type instanceof net.sourceforge.czt.oz.ast.ClassRefType) {
      ClassRefType ctype = (ClassRefType) type;
      result = classRefTypeToString(ctype);
    }
    else {
      result = type.toString();
    }
    return result;
  }

  public String classRefTypeToString(ClassRefType ctype)
  {
    String result = new String();
    RefName className = ctype.getThisClass().getRefName();
    result += "(CLASS " + className + "\n";

    ClassSig csig = ctype.getClassSig();
    result += "\tATTR(" + className + ")\n";
    for (Object o : csig.getAttribute()) {
      NameTypePair pair = (NameTypePair) o;
      result += "\t\t" + pair.getName() + " : " + pair.getType() + "\n";
    }
    result += "\tSTATE(" + className + ")\n";
    for (Object o : csig.getState().getNameTypePair()) {
      NameTypePair pair = (NameTypePair) o;
      result += "\t\t" + pair.getName() + " : " + toString(pair.getType()) + "\n";
    }
    result += "\tOPS(" + className + ")\n";
    for (Object o : csig.getOperation()) {
      NameSignaturePair p = (net.sourceforge.czt.oz.ast.NameSignaturePair) o;
      result += "\t\t" + p.getName() + " : " + p.getSignature();
    }
    result += ")";
    return result;
  }
}
