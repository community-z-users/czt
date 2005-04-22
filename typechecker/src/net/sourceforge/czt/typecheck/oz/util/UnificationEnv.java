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

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.oz.impl.*;

/**
 * Provides unification of types.
 */
public class UnificationEnv
  extends net.sourceforge.czt.typecheck.z.util.UnificationEnv
{
  //true if and only if strong unification is to be used
  protected boolean strong_ = true;

  public UnificationEnv(ZFactory zFactory)
  {
    super(zFactory);
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

  protected UResult unifyVarClassType(VariableClassType vType, Type2 type)
  {
    UResult result = FAIL;
    if (type instanceof ClassType) {
      ClassType classType = (ClassType) type;
      if (vType.getValue() != vType) {
        assert vType.getTypes().size() > 0;
        result = unify(vType.getValue(), classType);
      }
      else {
        if (vType.getTypes().size() == 0) {
          vType.getTypes().add(classType);
          vType.complete();
          result = SUCC;
        }
      }
    }
    else if (type instanceof VariableType || type instanceof UnknownType) {
      result = super.unify(vType, type);
    }
    return result;
  }

  protected UResult unifyClassType(ClassType typeA, ClassType typeB)
  {
    UResult result = SUCC;
    List<ClassRef> classRefsA = typeA.getClassSig().getClasses();
    List<ClassRef> classRefsB = typeB.getClassSig().getClasses();
    for (ClassRef classRefA : classRefsA) {
      ClassRef classRefB = findRef(classRefA.getRefName(), classRefsB);
      if (classRefB == null) {
        result = FAIL;
        break;
      }
      if (!renamesEqual(classRefA, classRefB)) {
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

    if (result != FAIL) {
      unifyClassSig(typeA.getClassSig(), typeB.getClassSig());
      if (typeA instanceof ClassRefType && typeB instanceof ClassRefType) {
        ClassRefType cTypeA = (ClassRefType) typeA;
        ClassRefType cTypeB = (ClassRefType) typeB;
        if (cTypeA.getThisClass() == null) {
          setInfo(cTypeA, cTypeB);
        }
        else if (cTypeB.getThisClass() == null) {
          setInfo(cTypeB, cTypeA);
        }
      }
      else if (typeA instanceof ClassPolyType && typeB instanceof ClassPolyType) {
        ClassPolyType cTypeA = (ClassPolyType) typeA;
        ClassPolyType cTypeB = (ClassPolyType) typeB;
        if (cTypeA.getRootClass() == null) {
          cTypeA.setRootClass(cTypeB.getRootClass());
        }
        else if (cTypeA.getRootClass() == null) {
          cTypeB.setRootClass(cTypeA.getRootClass());
        }
      }
    }

    return result;
  }

  protected void setInfo(ClassRefType typeA, ClassRefType typeB)
  {
    typeA.setThisClass(typeB.getThisClass());
    typeA.setVisibilityList(typeB.getVisibilityList());
    typeA.getSuperClass().addAll(typeB.getSuperClass());
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

  protected boolean renamesEqual(ClassRef classRefA, ClassRef classRefB)
  {
    boolean result = true;
    List<NameNamePair> pairsA = classRefA.getNameNamePair();
    for (NameNamePair pairA : pairsA) {
      NameNamePair pairB = findPair(pairA.getOldName(), classRefB);
      if (!pairA.getNewName().equals(pairB.getNewName())) {
        result = false;
        break;
      }
    }
    return result;
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
      if (refName.equals(classRef.getRefName())) {
        result = classRef;
      }
    }
    return result;
  }
}
