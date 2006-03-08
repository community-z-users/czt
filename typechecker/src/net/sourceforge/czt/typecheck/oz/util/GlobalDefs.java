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
package net.sourceforge.czt.typecheck.oz.util;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.util.OzString;

import net.sourceforge.czt.typecheck.oz.impl.*;

public class GlobalDefs
  extends net.sourceforge.czt.typecheck.z.util.GlobalDefs
{
  //non-safe typecast
  public static ClassType classType(Object o)
  {
    return (ClassType) o;
  }

  //non-safe typecast
  public static VariableClassSig variableClassSig(Object o)
  {
    return (VariableClassSig) o;
  }

  //unfold any references to variable class types in a type
  public static Type2 resolveVariableClassType(Type2 type)
  {
    Type2 result = resolve(type);
    if (result instanceof VariableClassType) {
      VariableClassType vClassType = (VariableClassType) result;
      if (vClassType.getCandidateType() != null) {
	result = vClassType.getCandidateType();
      }
    }
    else if (result instanceof PowerType) {
      PowerType powerType = (PowerType) result;
      Type2 resolved = resolveVariableClassType(powerType.getType());
      powerType.setType(resolved);
    }
    else if (result instanceof ProdType) {
      ProdType prodType = (ProdType) result;
      for (int i = 0; i < prodType.getType().size(); i++) {
	Type2 resolved = resolveVariableClassType(prodType.getType().get(i));
	prodType.getType().set(i, resolved);
      }
    }
    else if (result instanceof SchemaType) {
      Signature signature = ((SchemaType) result).getSignature();
      for (NameTypePair pair : signature.getNameTypePair()) {
	Type2 resolved = resolveVariableClassType(unwrapType(pair.getType()));
	pair.setType(resolved);
      }
    }
    else if (result instanceof ClassType) {
      ClassSig cSig = ((ClassType) result).getClassSig();
      List<ClassRef> classRefs = cSig.getClasses();
      for (ClassRef classRef : classRefs) {
	for (int i = 0; i < classRef.getType().size(); i++) {
	  Type2 resolved = resolveVariableClassType(classRef.getType().get(i));
	  classRef.getType().set(i, resolved);
	}
      }
    }
    return result;
  }

  //check if a name is in a signature's visibility list
  public static boolean isVisible(RefName refName, Type2 type)
  {
    boolean result = true;
    if (type instanceof ClassRefType) {
      ClassRefType classRefType = (ClassRefType) type;
      result = classRefType.getVisibilityList() == null ||
        classRefType.getVisibilityList().getRefName().contains(refName);
    }
    return result;
  }

  public static boolean isPowerClassRefType(Type2 type)
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

  public static boolean contains(List<ClassRef> list, ClassRef classRef)
  {
    boolean result = false;
    for (ClassRef element : list) {
      if (namesEqual(classRef.getZRefName(), element.getZRefName())) {
        result = true;
        break;
      }
    }
    return result;
  }

  public static NameSignaturePair findNameSigPair(ZDeclName zDeclName,
						  List<NameSignaturePair> pairs)
  {
    NameSignaturePair result = null;
    //find the pair that has this name
    for(NameSignaturePair pair : pairs) {
      if (namesEqual(zDeclName, pair.getZDeclName())) {
        result = pair;
        break;
      }
    }
    return result;
  }

  //find a NameSignaturePair in a class signature
  public static NameSignaturePair findOperation(ZDeclName zDeclName, ClassSig cSig)
  {
    NameSignaturePair result = findNameSigPair(zDeclName, cSig.getOperation());
    return result;
  }

  public static boolean isSelfName(ZDeclName zDeclName)
  {
    boolean result = zDeclName.getWord().equals(OzString.SELF) &&
      zDeclName.getStroke().size() == 0;
    return result;
  }
}
