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
package net.sourceforge.czt.typecheck.util.impl;

import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;

/**
 * Recursively clones terms.
 */
public class CloningVisitor
  implements
    GenericTypeVisitor,
    PowerTypeVisitor,
    GenParamTypeVisitor,
    GivenTypeVisitor,
    SchemaTypeVisitor,
    SignatureVisitor,
    ProdTypeVisitor,
    ClassRefTypeVisitor,
    ClassSigVisitor,
    VariableTypeVisitor,
    UnknownTypeVisitor,
    DeclNameVisitor,
    RefNameVisitor
{
  /** A TypeFactory. */
  protected Factory factory_ = null;

  /** List of generic names if the type is a GenericType. */
  protected List<DeclName> params_ = null;

  public CloningVisitor(Factory factory)
  {
    factory_ = factory;
    params_ = list();
  }

  public Object visitGenericType(GenericType genericType)
  {
    Type2 type = genericType.getType();
    Type2 optionalType = genericType.getOptionalType();
    List<DeclName> declNames = genericType.getName();

    List<DeclName> clonedNames = list();
    for (DeclName declName : declNames) {
      DeclName clonedName = (DeclName) declName.accept(this);
      clonedNames.add(clonedName);
    }

    params_.addAll(clonedNames);

    Type2 clonedType = (Type2) type.accept(this);
    Type2 clonedOptionalType = null;
    if (optionalType != null) {
      clonedOptionalType = (Type2) optionalType.accept(this);
    }

    params_.clear();
    GenericType clonedGenericType =
      factory_.createGenericType(clonedNames, clonedType, clonedOptionalType);

    //copy the annotations
    copyAnns(genericType, clonedGenericType);

    return clonedGenericType;
  }

  public Object visitPowerType(PowerType powerType)
  {
    Type baseType = powerType.getType();
    Type2 clonedBaseType = (Type2) baseType.accept(this);
    PowerType clonedPowerType = factory_.createPowerType(clonedBaseType);

    //copy the annotations
    copyAnns(powerType, clonedPowerType);

    return clonedPowerType;
  }

  public Object visitGenParamType(GenParamType genParamType)
  {
    DeclName declName = genParamType.getName();
    DeclName clonedDeclName = (DeclName) declName.accept(this);
    GenParamType clonedGenParamType =
      factory_.createGenParamType(clonedDeclName);
    return clonedGenParamType;
  }

  public Object visitGivenType(GivenType givenType)
  {
    DeclName declName = givenType.getName();
    DeclName clonedDeclName = (DeclName) declName.accept(this);
    GivenType clonedGivenType = factory_.createGivenType(clonedDeclName);
    return clonedGivenType;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    List<NameTypePair> clonedPairs = list();
    Signature signature = schemaType.getSignature();
    Signature clonedSignature = (Signature) signature.accept(this);
    SchemaType clonedSchemaType = factory_.createSchemaType(clonedSignature);
    return clonedSchemaType;
  }

  public Object visitSignature(Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    List<NameTypePair> clonedPairs = list();
    for (NameTypePair pair : pairs) {
      DeclName clonedDeclName = (DeclName) pair.getName().accept(this);
      Type clonedType = (Type) pair.getType().accept(this);
      NameTypePair clonedPair =
        factory_.createNameTypePair(clonedDeclName, clonedType);
      clonedPairs.add(clonedPair);
    }

    Signature clonedSignature = factory_.createSignature(clonedPairs);
    return clonedSignature;
  }

  public Object visitProdType(ProdType prodType)
  {
    List<Type> clonedTypes = list();
    List<Type> types = prodType.getType();
    for (Type type : types) {
      Type clonedType = (Type) type.accept(this);
      clonedTypes.add(clonedType);
    }

    ProdType clonedProdType = factory_.createProdType(clonedTypes);
    return clonedProdType;
  }

  public Object visitClassRefType(ClassRefType classRefType)
  {
    ClassSig classSig = classRefType.getClassSig();
    ClassSig clonedClassSig = (ClassSig) classSig.accept(this);

    ClassRef thisClass = classRefType.getThisClass();
    ClassRef clonedThis = (ClassRef) thisClass.accept(this);

    List<ClassRef> superClasses = classRefType.getSuperClass();
    List<ClassRef> clonedSuperClasses = list();
    for (ClassRef superClass : superClasses) {
      ClassRef clonedRef = (ClassRef) superClass.accept(this);
      clonedSuperClasses.add(clonedRef);
    }

    ClassRefType clonedClassRefType =
      factory_.createClassRefType(clonedClassSig, clonedThis,
                                  clonedSuperClasses,
                                  classRefType.getVisibilityList());

    return clonedClassRefType;
  }

  public Object visitClassSig(ClassSig classSig)
  {
    Signature clonedState = null;
    if (classSig.getState() != null) {
      clonedState =
        (Signature) classSig.getState().accept(this);
    }

    List<ClassRef> classes = classSig.getClasses();
    List<ClassRef> clonedClasses = list();
    for (ClassRef aClass : classes) {
      clonedClasses.add((ClassRef) aClass.accept(this));
    }

    List<NameTypePair> attr = classSig.getAttribute();
    List<NameTypePair> clonedAttr = list();
    for (NameTypePair pair : attr) {
      DeclName clonedName = (DeclName) pair.getName().accept(this);
      Type clonedType = (Type) pair.getType().accept(this);
      NameTypePair clonedPair =
        factory_.createNameTypePair(clonedName, clonedType);
      clonedAttr.add(clonedPair);
    }

    List<NameSignaturePair> ops = classSig.getOperation();
    List<NameSignaturePair> clonedOps = list();
    for (NameSignaturePair pair : ops) {
      DeclName clonedName = (DeclName) pair.getName().accept(this);
      Signature clonedSig = (Signature) pair.getSignature().accept(this);
      NameSignaturePair clonedPair =
        factory_.createNameSignaturePair(clonedName, clonedSig);
      clonedOps.add(clonedPair);
    }

    return factory_.createClassSig(clonedClasses, clonedState,
                                   clonedAttr, clonedOps);
  }

  public Object visitVariableType(VariableType vType)
  {
    VariableType clonedVType = factory_.createVariableType(vType.getName());
    if (vType.getValue() != vType) {
      clonedVType.setValue(vType.getValue());
    }
    return clonedVType;
  }

  public Object visitUnknownType(UnknownType unknownType)
  {
    return unknownType;
  }

  public Object visitDeclName(DeclName declName)
  {
    DeclName clonedDeclName =
      factory_.createDeclName(declName.getWord(),
                              declName.getStroke(),
                              declName.getId());

    //include type annotations
    TypeAnn typeAnn = (TypeAnn) declName.getAnn(TypeAnn.class);
    if (typeAnn != null) {
      clonedDeclName.getAnns().add(typeAnn);
    }
    return clonedDeclName;
  }

  public Object visitRefName(RefName refName)
  {
    RefName clonedRefName =
      factory_.createRefName(refName.getWord(),
                             refName.getStroke(),
                             refName.getDecl());

    //include type annotations
    TypeAnn typeAnn = (TypeAnn) refName.getAnn(TypeAnn.class);
    if (typeAnn != null) {
      clonedRefName.getAnns().add(typeAnn);
    }
    return clonedRefName;

  }

  protected void copyAnns(Type src, Type dest)
  {
    dest.getAnns().addAll(src.getAnns());
  }

  protected List list()
  {
    return new ArrayList();
  }
}
