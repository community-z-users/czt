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
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.typecheck.z.util.*;
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

  //non-safe typecast
  protected static ClassType classType(Object o)
  {
    return (ClassType) o;
  }

  //non-safe typecast
  protected static VariableClassSig variableClassSig(Object o)
  {
    return (VariableClassSig) o;
  }

  //the operation expr checker
  protected Checker opExprChecker()
  {
    return typeChecker_.opExprChecker_;
  }

  //the current class name
  protected DeclName className()
  {
    return typeChecker_.className_;
  }

  //set the name of the current class
  protected void setClassName(DeclName declName)
  {
    typeChecker_.className_ = declName;
  }

  //the last of primary state variables in the current class
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
    return TypeCheckUtils.typecheck(termA, sectInfo);
  }

  protected void error(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = errorAnn(termA, error, params);
    error(termA, errorAnn);
  }

  protected ErrorAnn errorAnn(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
                                     sectName(), nearestLocAnn(termA));
    return errorAnn;
  }

  protected ErrorAnn errorAnn(TermA termA, String error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error, params, sectInfo(),
                                     sectName(), nearestLocAnn(termA));
    return errorAnn;
  }

  //check if a name is in a signature's visibility list
  protected boolean isVisible(RefName refName, ClassType classType)
  {
    boolean result = true;
    if (classType instanceof ClassRefType) {
      ClassRefType classRefType = (ClassRefType) classType;
      result = classRefType.getVisibilityList() == null ||
        classRefType.getVisibilityList().getRefName().contains(refName);
    }
    return result;
  }

  //get the type of "self"
  protected ClassRefType getSelfType()
  {
    RefName refName = factory().createRefName(OzString.SELF, list(), null);
    RefExpr refExpr = factory().createRefExpr(refName, list(), Boolean.FALSE);
    Type2 selfType = (Type2) refExpr.accept(exprChecker());

    assert selfType instanceof ClassRefType;
    return (ClassRefType) selfType;
  }

  //take the intersection of 2 signatures
  protected Signature intersect(Signature sigA, Signature sigB)
  {
    Signature signature = factory().createSignature();
    List<NameTypePair> pairsA = sigA.getNameTypePair();
    List<NameTypePair> pairsB = sigB.getNameTypePair();
    for (NameTypePair pairA : pairsA) {
      NameTypePair pairB = findInSignature(pairA.getName(), sigB);
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
      UResult unified = unify(op.getSignature(), existing.getSignature());
      if (unified == FAIL) {
        Object [] params = {opName, op.getSignature(), existing.getSignature()};
        error(opName, ErrorMessage.INCOMPATIBLE_OP_OVERRIDING, params);
      }
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
  protected void checkForDuplicates(ClassSig cSig)
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
          Object [] params = {first, className()};
          error(first, ErrorMessage.REDECLARED_NAME_IN_CLASSPARA, params);
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
        NameTypePair foundPair = findInSignature(sName, lSig);
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

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = factory().createUnknownType();

    //if this is a class type, instantiate it
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      ClassSig cSig = classType.getClassSig();

      if (!(cSig instanceof VariableClassSig)) {
        //instantiate the state
        Signature state = cSig.getState();
        if (state != null) {
          instantiate(state);
        }

        //instantiate the attributes
        List<NameTypePair> attrs = cSig.getAttribute();
        for (NameTypePair pair : attrs) {
          Type2 pairType = unwrapType(pair.getType());
          instantiate(pairType);
        }

        //instantiate the operations
        List<NameSignaturePair> ops = cSig.getOperation();
        for (NameSignaturePair pair : ops) {
          Signature signature = pair.getSignature();
          instantiate(signature);
        }

        //instaniate the class references
        List<ClassRef> classRefs = cSig.getClasses();
        for (ClassRef classRef : classRefs) {
          List<Type2> types = classRef.getType2();
          for (int i = 0; i < types.size(); i++) {
            Type2 replaced = instantiate(types.get(i));
            types.set(i, replaced);
          }
        }
      }

      ClassRef classRef = null;
      if (type instanceof ClassRefType) {
        ClassRefType classRefType = (ClassRefType) type;
        classRef = classRefType.getThisClass();
      }
      else if (type instanceof ClassPolyType) {
        ClassPolyType classPolyType = (ClassPolyType) type;
        classRef = classPolyType.getRootClass();
      }

      if (classRef != null) {
        List<Type2> types = classRef.getType2();
        for (Type2 next : types) {
          instantiate(next);
        }
      }

      result = classType;
    }
    //if not a class type, use the Z typechecker's instantiate method
    else {
      result = super.instantiate(type);
    }

    return result;
  }

  protected Type getType(RefName name)
  {
    Type type = super.getType(name);

    //if the name we are looking up is this class name, then we clone
    //the type because for a generic class, the parameters must be
    //instantiated even when referenced from within itself
    if (className() != null &&
        className().getWord().equals(name.getWord()) &&
        className().getStroke().equals(name.getStroke())) {
      type = (Type) factory().cloneTerm(type);
    }

    return type;
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

  protected boolean isPowerClassRefType(Type2 type)
  {
    boolean result = false;
    if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      if (powerType.getType() instanceof ClassRefType) {
        result = true;
      }
    }
    return result;
  }

  //find an attribute in a class signature
  protected NameTypePair findAttribute(DeclName declName, ClassSig cSig)
  {
    NameTypePair result = findInPairList(declName, cSig.getAttribute());
    return result;
  }

  //find a state variable in a class signature
  protected NameTypePair findStateDecl(DeclName declName, ClassSig cSig)
  {
    List<NameTypePair> decls = cSig.getState().getNameTypePair();
    NameTypePair result = findInPairList(declName, decls);
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

  protected boolean contains(List<ClassRef> list, ClassRef classRef)
  {
    boolean result = false;
    for (ClassRef element : list) {
      if (classRef.getRefName().equals(element.getRefName())) {
        result = true;
        break;
      }
    }
    return result;
  }
}
