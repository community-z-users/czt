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
package net.sourceforge.czt.typecheck.oz.impl;

import java.util.List;

import static net.sourceforge.czt.typecheck.oz.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.z.impl.*;
import net.sourceforge.czt.typecheck.oz.util.GlobalDefs;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
  extends net.sourceforge.czt.typecheck.z.impl.Factory
{
  /** The OzFactory that is used to create wrapped types. */
  protected OzFactory ozFactory_;

  public Factory()
  {
    zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    ozFactory_ = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
  }

  public Factory(ZFactory zFactory)
  {
    zFactory_ = zFactory;
    ozFactory_ = new net.sourceforge.czt.oz.impl.OzFactoryImpl();
  }

  public Factory(ZFactory zFactory, OzFactory ozFactory)
  {
    zFactory_ = zFactory;
    ozFactory_ = ozFactory;
  }

  public OzFactory getOzFactory()
  {
    return ozFactory_;
  }

  public ClassRef createClassRef()
  {
    ClassRef classRef = ozFactory_.createClassRef();
    ClassRef result = new ClassRefImpl(classRef);
    return result;
  }

  public ClassRef createClassRef(ZDeclName zDeclName,
				 List<Type2> type,
				 List<NewOldPair> pairs)
  {
    RefName refName = createZRefName(zDeclName);
    ClassRef result = createClassRef(refName, type, pairs);
    return result;
  }

  public ClassRef createClassRef(ZDeclName zDeclName)
  {
    ClassRef result = createClassRef(zDeclName,
				     this.<Type2>list(),
				     this.<NewOldPair>list());
    return result;
  }

  public ClassRef createClassRef(RefName refName,
				 List<Type2> type,
				 List<NewOldPair> pairs)
  {
    ClassRef classRef = ozFactory_.createClassRef(refName, type, pairs);
    ClassRef result = new ClassRefImpl(classRef);
    return result;
  }

  public ClassRefType createClassRefType()
  {
    ClassRefType classRefType = ozFactory_.createClassRefType();
    ClassSig classSig = createVariableClassSig();
    classRefType.setClassSig(classSig);
    ClassRefType result = new ClassRefTypeImpl(classRefType);
    return result;
  }

  public ClassRefType createClassRefType(ClassSig classSig,
                                         ClassRef thisClass,
                                         List<ClassRef> superClass,
                                         VisibilityList visibilityList,
                                         List<DeclName> primary)
  {
    ClassRefType classRefType =
      ozFactory_.createClassRefType(classSig, thisClass,
                                    superClass, visibilityList, primary);
    ClassRefType result = new ClassRefTypeImpl(classRefType);
    return result;
  }

  public ClassPolyType createClassPolyType()
  {
    ClassSig classSig = createVariableClassSig();
    ClassPolyType classPolyType = ozFactory_.createClassPolyType();
    classPolyType.setClassSig(classSig);
    ClassPolyType result = new ClassPolyTypeImpl(classPolyType);
    return result;
  }

  public ClassPolyType createClassPolyType(ClassSig classSig, ClassRef rootClass)
  {
    ClassPolyType classPolyType =
      ozFactory_.createClassPolyType(classSig, rootClass);
    ClassPolyType result = new ClassPolyTypeImpl(classPolyType);
    return result;
  }

  public ClassUnionType createClassUnionType()
  {
    ClassSig classSig = createClassSig();
    ClassUnionType result = createClassUnionType(classSig);
    return result;
  }

  public ClassUnionType createClassUnionType(ClassSig classSig)
  {
    ClassUnionType classUnionType = ozFactory_.createClassUnionType(classSig);
    ClassUnionType result = new ClassUnionTypeImpl(classUnionType);
    return result;
  }

  public VariableClassType createVariableClassType()
  {
    return new VariableClassType(this);
  }

  public VariableClassSig createVariableClassSig()
  {
    return new VariableClassSig(this);
  }

  public ClassSig createClassSig()
  {
    return ozFactory_.createClassSig();
  }

  public ClassSig createClassSig(List<ClassRef> classes,
                                 Signature state,
                                 List<NameTypePair> attribute,
                                 List<NameSignaturePair> operation)
  {
    return ozFactory_.createClassSig(classes, state,
                                     attribute, operation);
  }

  public NameSignaturePair createNameSignaturePair(DeclName declName,
                                                   Signature signature)
  {
    NameSignaturePair pair =
      ozFactory_.createNameSignaturePair(declName, signature);
    NameSignaturePair result = new NameSignaturePairImpl(pair);
    return result;
  }

  public PowerType createBoolType()
  {
    Signature signature = createSignature();
    SchemaType schemaType = createSchemaType(signature);
    PowerType result = createPowerType(schemaType);
    return result;
  }

  public PowerType createOIDType()
  {
    List<ClassRef> classes = list();
    Signature state = createSignature();
    List<NameTypePair> attrs = list();
    List<NameSignaturePair> ops = list();    
    ClassSig classSig = createClassSig(classes, state, attrs, ops);
    ClassUnionType cuType = createClassUnionType(classSig);
    PowerType result = createPowerType(cuType);
    return result;
  }

  public ClassUnionExpr createClassUnionExpr()
  {
    return ozFactory_.createClassUnionExpr();
  }
}
