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

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.VariableType;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * Provides unification of types.
 */
public class UnificationEnv
  extends net.sourceforge.czt.typecheck.z.util.UnificationEnv
{
  /** A Factory. */
  protected Factory factory_ = null;

  //true if and only if strong unification is to be used
  protected boolean strong_;

  public UnificationEnv(Factory factory, boolean strong)
  {
    super(factory);
    factory_ = factory;
    strong_ = strong;
  }

  public UnificationEnv(Factory factory)
  {
    this(factory, false);
    factory_ = factory;
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
    if (typeA instanceof VariableClassType) {
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

  protected UResult unifyVariableType(VariableType vType, Type2 type)
  {
    UResult result = FAIL;
    if (!strong_ && type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      if (vType.getValue() != vType) {
        result = unify(vType.getValue(), classType);
      }
      else {
        VariableClassType vClassType = factory_.createVariableClassType();
        vClassType.setCandidateType(classType);
	vType.setValue(vClassType);
	result = PARTIAL;
      }
    }
    else {
      result = super.unifyVariableType(vType, type);
    }
    return result;
  }

  protected UResult unifyVarClassType(VariableClassType vType, Type2 type)
  {
    UResult result = FAIL;
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      if (strong_) {
        result = strongUnifyVarClassType(vType, classType);
      }
      else {
        result = weakUnifyVarClassType(vType, classType);
      }
    }
    else if (type instanceof VariableType || type instanceof UnknownType) {
      result = super.unify(type, vType);
    }
    return result;
  }

  protected UResult strongUnifyVarClassType(VariableClassType vType,
                                            ClassType classType)
  {
    UResult result = FAIL;
    if (vType.getValue() != vType) {
      result = unify(vType.getValue(), classType);
    }
    else {
      if (contains(classType, vType)) {
        result = FAIL;
      }
      else {
	vType.setValue(classType);
	result = unify(vType.getValue(), classType);
      }
    }
    return result;
  }

  protected UResult weakUnifyVarClassType(VariableClassType vClassType,
                                          ClassType classType)
  {
    UResult result = SUCC;
    if (vClassType.getCandidateType() == null) {
      vClassType.setCandidateType(classType);
    }
    else {
      ClassType candidateType = vClassType.getCandidateType();
      ClassType newType = checkCompatibility(candidateType, classType);
      if (newType != null) {
	vClassType.setCandidateType(newType);
      }
      result = (newType == null) ? FAIL : SUCC;
    }
    return result;
  }

  protected UResult unifyClassType(ClassType typeA, ClassType typeB)
  {
    UResult result = FAIL;
    if (strong_) {
      result = strongUnifyClassType(typeA, typeB);
    }
    else {
      result = weakUnifyClassType(typeA, typeB);
    }
    return result;
  }

  protected UResult weakUnifyClassType(ClassType typeA, ClassType typeB)
  {
    UResult result = FAIL;
    List<ClassRef> classRefsA = typeA.getClassSig().getClasses();
    List<ClassRef> classRefsB = typeB.getClassSig().getClasses();
    if (classRefsA.size() == 0 || classRefsB.size() == 0) {
      result = SUCC;
    }
    else {
      for (ClassRef classRefA : classRefsA) {
        ClassRef classRefB = findRef(classRefA.getRefName(), classRefsB);
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
    List<ClassRef> classRefsA = typeA.getClassSig().getClasses();
    List<ClassRef> classRefsB = typeB.getClassSig().getClasses();
    if (classRefsA.size() != classRefsB.size()) {
      result = FAIL;
    }
    else {
      for (ClassRef classRefA : classRefsA) {
        ClassRef classRefB = findRef(classRefA.getRefName(), classRefsB);
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

  protected void unifyClassSig(ClassSig sigA, ClassSig sigB)
  {
    if (sigA instanceof VariableClassSig) {
      VariableClassSig vSig = (VariableClassSig) sigA;
      vSig.setValue(sigB);
    }
    else if (sigB instanceof VariableClassSig) {
      VariableClassSig vSig = (VariableClassSig) sigB;
      vSig.setValue(sigA);
    }
  }

  protected UResult instantiations(ClassRef classRefA, ClassRef classRefB)
  {
    UResult result = SUCC;
    List<Type2> typesA = classRefA.getType2();
    List<Type2> typesB = classRefB.getType2();
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

  protected NameNamePair findPair(RefName oldName, ClassRef classRef)
  {
    NameNamePair result = null;
    List<NameNamePair> pairs = classRef.getNameNamePair();
    for (NameNamePair pair : pairs) {
      if (oldName.equals(pair.getOldName())) {
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
      if (refName.getWord().equals(classRef.getRefName().getWord()) &&
          refName.getStroke().equals(classRef.getRefName().getStroke())) {
        result = classRef;
      }
    }
    return result;
  }

  protected ClassType checkCompatibility(ClassType classTypeA,
					 ClassType classTypeB)
  {
    ClassSig cSigA = classTypeA.getClassSig();
    ClassSig cSigB = classTypeB.getClassSig();
    List<NameTypePair> attrsA = cSigA.getAttribute();
    List<NameTypePair> attrsB = cSigB.getAttribute();
    List<NameTypePair> stateA = cSigA.getState().getNameTypePair();
    List<NameTypePair> stateB = cSigB.getState().getNameTypePair();

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

    List<NameSignaturePair> opsA = cSigA.getOperation();
    List<NameSignaturePair> opsB = cSigB.getOperation();
    List<NameSignaturePair> ops = checkOpCompatibility(opsA, opsB);
    if (ops == null) {
      return null;
    }

    //add the class references
    List<ClassRef> classes = list();
    for (ClassRef classRef : cSigA.getClasses()) {
      if (!contains(classes, classRef)) {
	classes.add(classRef);
      }
    }
    for (ClassRef classRef : cSigB.getClasses()) {
      if (!contains(classes, classRef)) {
	classes.add(classRef);
      }
    }    
    Signature state = factory_.createSignature(statePairs);
    ClassSig cSig = factory_.createClassSig(classes, state, attrs, ops);
    ClassType result = null;
    if (classes.size() == 1) {
      result = classTypeA;
    }
    else {
      result = factory_.createClassUnionType(cSig);
    }
    return result;
  }

  protected List<NameTypePair> 
    checkCompatibility(List<NameTypePair> pairsA,
		       List<NameTypePair> pairsB,
		       List<NameTypePair> altPairs)
  {
    List<NameTypePair> result = list();
    //check compatibility of attributes and state variables
    for (NameTypePair first : pairsA) {
      DeclName firstName = first.getName();
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
    List<NameSignaturePair> result = list();
    for (NameSignaturePair first : pairsA) {
      DeclName firstName = first.getName();
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

  protected static boolean contains(List<ClassRef> list, ClassRef classRef)
  {
    return GlobalDefs.contains(list, classRef);
  }
}
