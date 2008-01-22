/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.oz.util;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.VariableType;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.oz.impl.*;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * Provides unification of types.
 */
public class UnificationEnv
  extends net.sourceforge.czt.typecheck.z.util.UnificationEnv
{
  //true if and only if strong unification is to be used
  protected boolean strong_;

  public UnificationEnv(Factory factory, boolean strong)
  {
    super(factory);
    strong_ = strong;
  }

  public UnificationEnv(Factory factory)
  {
    this(factory, false);
  }

  public void setStrong(boolean strong)
  {
    strong_ = strong;
  }

  public UResult strongUnify(Type2 typeA, Type2 typeB)
  {
    final boolean previous = strong_;
    strong_ = true;
    UResult result = this.unify(typeA, typeB);
    strong_ = previous;
    return result;
  }

  public UResult weakUnify(Type2 typeA, Type2 typeB)
  {
    final boolean previous = strong_;
    strong_ = false;
    UResult result = this.unify(typeA, typeB);
    strong_ = previous;
    return result;
  }

  public UResult unify(Type2 typeA, Type2 typeB)
  {
    UResult result = FAIL;
    if (isUnknownType(typeA)) {
      result = unifyUnknownType(unknownType(typeA), typeB);
    }
    else if (isUnknownType(typeB)) {
      result = unifyUnknownType(unknownType(typeB), typeA);
    }
    else if (typeA instanceof VariableClassType) {
      result = unifyVarClassType((VariableClassType) typeA, typeB);
    }
    else if (typeB instanceof VariableClassType) {
      result = unifyVarClassType((VariableClassType) typeB, typeA);
    }
    else if (typeA instanceof ClassType && typeB instanceof ClassType) {
      result = unifyClassType((ClassType) typeA, (ClassType) typeB);
    }
    else {
      result = super.unify(typeA, typeB);
    }
    return result;
  }

  protected UResult unifyUnknownType(UnknownType uType, Type2 type2)
  {
    UResult result = PARTIAL;
    if (type2 instanceof VariableClassType ||
        (type2 instanceof PowerType &&
         powerType(type2) instanceof VariableClassType)) {
      result = PARTIAL;
    }
    else {
      result = super.unifyUnknownType(uType, type2);
    }

    return result;
  }

  protected UResult unifyVariableType(VariableType vType, Type2 type)
  {
    UResult result = FAIL;
    //if this variable is not ground
    if (vType.getValue() == vType) {
      //if we are using weak typing, and the type is a class type,
      //then create a variable class type with 'type' as its candidate
      if (!strong_ && type instanceof ClassType) {
        ClassType classType = (ClassType) type;
        VariableClassType vClassType = getFactory().createVariableClassType();
        vClassType.setCandidateType(classType);
        vType.setValue(vClassType);
        result = PARTIAL;
      }
      //if this is not a class type, or we are using strong typing,
      //continue as normal
      else {
        result = super.unifyVariableType(vType, type);
      }
    }
    //if the variable is already ground, then unify the ground value with type2
    else {
      result = unify(vType.getValue(), type);
    }
    return result;
  }

  protected UResult unifyVarClassType(VariableClassType vClassType, Type2 type)
  {
    UResult result = FAIL;
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      result = strong_ ?
        strongUnifyVarClassType(vClassType, classType) :
        weakUnifyVarClassType(vClassType, classType);
    }
    else if (type instanceof VariableType || type instanceof UnknownType) {
      result = super.unify(type, vClassType);
    }
    return result;
  }

  protected UResult strongUnifyVarClassType(VariableClassType vClassType,
                                            ClassType classType)
  {
    //strong unification of a variable type is variable type unification
    UResult result = super.unifyVariableType(vClassType, classType);
    return result;
  }

  protected UResult weakUnifyVarClassType(VariableClassType vClassTypeA,
                                          ClassType classType)
  {
    UResult result = PARTIAL;

    //if this variable is not ground
    if (vClassTypeA.getValue() == vClassTypeA) {
      ClassType candidateTypeA = vClassTypeA.getCandidateType();
      //if we have the same variable, the result is PARTIAL
      if (vClassTypeA == classType) {
        result = PARTIAL;
      }
      //if a has no candidate type yet, the classType is its type
      else if (candidateTypeA == null) {
        if (classType instanceof VariableClassType) {
          vClassTypeA.setValue(classType);
        }
        else {
          vClassTypeA.setCandidateType(classType);
        }
      }
      //if classType is a variable class
      else if (classType instanceof VariableClassType) {
        VariableClassType vClassTypeB = (VariableClassType) classType;
        ClassType candidateTypeB = vClassTypeB.getCandidateType();

        //if vClassTypeB does not have a candidate type
        if (candidateTypeB == null) {
          result = weakUnifyVarClassType(vClassTypeB, vClassTypeA);
        }
        //if vClassTypeB does have a candidate type
        else {
          //calculate the union and set this as the new candidate type for both
          ClassType newCandidateType =
            checkCompatibility(candidateTypeA, candidateTypeB);
          if (newCandidateType != null) {
            vClassTypeA.setCandidateType(newCandidateType);
            vClassTypeB.setValue(vClassTypeA);
          }
          result = (newCandidateType == null) ? FAIL : PARTIAL;
        }
      }
      //if classType is not a variable
      else {
        //calculate the union and set this as the candidate type
        ClassType newCandidateType = checkCompatibility(candidateTypeA, classType);
        if (newCandidateType != null) {
          vClassTypeA.setCandidateType(newCandidateType);
        }
        result = (newCandidateType == null) ? FAIL : PARTIAL;
      }
    }
    //if this variable is already ground, the value with classType
    else {
      result = this.unify(vClassTypeA.getValue(), classType);
    }
    return result;
  }

  protected UResult unifyClassType(ClassType typeA, ClassType typeB)
  {
    UResult result = strong_ ?
      strongUnifyClassType(typeA, typeB) :
      weakUnifyClassType(typeA, typeB);
    return result;
  }

  protected UResult weakUnifyClassType(ClassType typeA, ClassType typeB)
  {
    UResult result = FAIL;
    List<ClassRef> classRefsA = typeA.getClasses();
    List<ClassRef> classRefsB = typeB.getClasses();
    if (classRefsA.size() == 0 || classRefsB.size() == 0) {
      result = SUCC;
    }
    else {
      for (ClassRef classRefA : classRefsA) {
        ClassRef classRefB = findRef(classRefA.getName(), classRefsB);
        if (classRefB != null) {
          UResult unified = instantiations(classRefA, classRefB);
          if (SUCC.equals(unified)) {
            result = SUCC;
          }
          else if (PARTIAL.equals(unified) && !SUCC.equals(result)) {
            result = PARTIAL;
          }
        }
      }
    }
    return result;
  }

  protected UResult strongUnifyClassType(ClassType typeA, ClassType typeB)
  {
    UResult result = SUCC;
    List<ClassRef> classRefsA = typeA.getClasses();
    List<ClassRef> classRefsB = typeB.getClasses();
    if (classRefsA.size() != classRefsB.size()) {
      result = FAIL;
    }
    else {
      for (ClassRef classRefA : classRefsA) {
        ClassRef classRefB = findRef(classRefA.getName(), classRefsB);
        if (classRefB == null) {
          result = FAIL;
          break;
        }
        UResult unified = instantiations(classRefA, classRefB);
        if (unified == FAIL) {
          result = FAIL;
          break;
        }
        else if (PARTIAL.equals(unified)) {
          result = PARTIAL;
        }
      }
    }
    return result;
  }

  protected UResult instantiations(ClassRef classRefA, ClassRef classRefB)
  {
    UResult result = SUCC;
    List<Type2> typesA = classRefA.getType();
    List<Type2> typesB = classRefB.getType();
    assert typesA.size() == typesB.size();
    for (int i = 0; i < typesA.size(); i++) {
      UResult unified = unify(typesA.get(i), typesB.get(i));
      if (unified == FAIL) {
        result = FAIL;
      }
      else if (unified == PARTIAL && !(result == FAIL)) {
        result = PARTIAL;
      }
    }
    return result;
  }

  protected NewOldPair findPair(ZName oldName, ClassRef classRef)
  {
    NewOldPair result = null;
    List<NewOldPair> pairs = classRef.getNewOldPair();
    for (NewOldPair pair : pairs) {
      if (oldName.equals(pair.getOldName())) {
        result = pair;
        break;
      }
    }
    return result;
  }

  protected ClassRef findRef(Name name, List<ClassRef> classRefs)
  {
    ClassRef result = null;
    for (ClassRef classRef : classRefs) {
      if (ZUtils.namesEqual(name, classRef.getName())) {
        result = classRef;
      }
    }
    return result;
  }

  protected ClassType checkCompatibility(ClassType classTypeA,
                                         ClassType classTypeB)
  {
    List<NameTypePair> attrsA = classTypeA.getAttribute();
    List<NameTypePair> attrsB = classTypeB.getAttribute();
    List<NameTypePair> stateA = classTypeA.getState().getNameTypePair();
    List<NameTypePair> stateB = classTypeB.getState().getNameTypePair();

    //check compatibility of attributes and state variables
    List<NameTypePair> attrs = checkCompatibility(attrsA, attrsB, stateB);
    if (attrs == null) {
      return null;
    }

    //check compatibility of operations
    List<NameTypePair> statePairs = checkCompatibility(stateA, stateB, attrsB);
    if (statePairs == null) {
      return null;
    }

    List<NameSignaturePair> opsA = classTypeA.getOperation();
    List<NameSignaturePair> opsB = classTypeB.getOperation();
    List<NameSignaturePair> ops = checkOpCompatibility(opsA, opsB);
    if (ops == null) {
      return null;
    }

    //add the class references
    ClassRefList classes = getFactory().createClassRefList();
    for (ClassRef classRef : classTypeA.getClasses()) {
      if (!contains(classes, classRef)) {
        classes.add(classRef);
      }
    }
    for (ClassRef classRef : classTypeB.getClasses()) {
      if (!contains(classes, classRef)) {
        classes.add(classRef);
      }
    }
    Signature state = getFactory().createSignature(statePairs);
    ClassType result = null;
    if (classes.size() == 1) {
      result = classTypeA;
    }
    else {
      result = getFactory().createClassUnionType(classes, state, attrs, ops);
    }
    return result;
  }

  protected List<NameTypePair> checkCompatibility(List<NameTypePair> pairsA,
                                                  List<NameTypePair> pairsB,
                                                  List<NameTypePair> altPairs)
  {
    List<NameTypePair> result = getFactory().list();
    //check compatibility of attributes and state variables
    for (NameTypePair first : pairsA) {
      ZName firstName = first.getZName();
      if (!isSelfName(firstName)) {
        NameTypePair second = findNameTypePair(firstName, pairsB);
        if (second != null) {
          Type2 firstType = unwrapType(first.getType());
          Type2 secondType = unwrapType(second.getType());
          UResult unified = unify(firstType, secondType);
          if (unified == FAIL) {
            return null;
          }
          else {
            result.add(first);
          }
        }
        //check that the attribute does not have a conflicting state variable
        second = findNameTypePair(firstName, altPairs);
        if (second != null) {
          Type2 firstType = unwrapType(first.getType());
          Type2 secondType = unwrapType(second.getType());
          UResult unified = unify(firstType, secondType);
          if (unified == FAIL) {
            return null;
          }
        }
      }
    }
    return result;
  }

  //check compatibility of operations
  protected List<NameSignaturePair>
    checkOpCompatibility(List<NameSignaturePair> pairsA,
                         List<NameSignaturePair> pairsB)
  {
    List<NameSignaturePair> result = getFactory().list();
    for (NameSignaturePair first : pairsA) {
      ZName firstName = first.getZName();
      NameSignaturePair second = findNameSigPair(firstName, pairsB);
      if (second != null) {
        Signature lSig = first.getSignature();
        Signature rSig = second.getSignature();
        UResult unified = unify(lSig, rSig);
        if (unified == FAIL) {
          return null;
        }
        else {
          result.add(first);
        }
      }
    }
    return result;
  }

  protected static boolean contains(ClassRefList list, ClassRef classRef)
  {
    return GlobalDefs.contains(list, classRef);
  }

  protected boolean contains(Term term, Object o, List<Term> preTerms)
  {
    //add this term to the list that has been checked, so that we can
    //check recursive type structures
    if (term instanceof ClassType) {
      preTerms.add(term);
    }
    return super.contains(term, o, preTerms);
  }

  protected Factory getFactory()
  {
    return (Factory) factory_;
  }

}
