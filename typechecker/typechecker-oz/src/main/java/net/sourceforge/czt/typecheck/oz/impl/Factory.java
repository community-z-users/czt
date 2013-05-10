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

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;

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

  public ClassRef createClassRef(ZName zName)
  {
    ClassRef result = createClassRef(zName,
                                     this.<Type2>list(),
                                     this.<NewOldPair>list());
    return result;
  }

  public ClassRef createClassRef(ZName zName,
                                 List<Type2> type,
                                 List<NewOldPair> pairs)
  {
    ClassRef classRef = ozFactory_.createClassRef(zName, type, pairs);
    ClassRef result = new ClassRefImpl(classRef);
    return result;
  }

  public ClassRefList createClassRefList()
  {
    ClassRefList result = ozFactory_.createClassRefList();
    return result;
  }

  public ClassRefList createClassRefList(List<? extends ClassRef> classes)
  {
    ClassRefList result = ozFactory_.createClassRefList(classes);
    return result;
  }

  public ClassRefType createClassRefType()
  {
    ClassRefType result = ozFactory_.createClassRefType();
    return result;
  }

  public ClassRefType createClassRefType(ClassRefList classes,
                                         Signature state,
                                         List<? extends NameTypePair> attribute,
                                         List<? extends NameSignaturePair> operation,
                                         ClassRef thisClass,
                                         List<? extends ClassRef> superClass,
                                         VisibilityList visibilityList,
                                         List<? extends Name> primary)
  {
    ClassRefList superClasses = ozFactory_.createClassRefList();
    superClasses.addAll(superClass);
    ClassRefType result =
      ozFactory_.createClassRefType(classes, state, attribute, operation, thisClass,
                                    superClasses, visibilityList, primary);
    return result;
  }

  public ClassPolyType createClassPolyType()
  {
    ClassPolyType result = ozFactory_.createClassPolyType();
    return result;
  }

  public ClassPolyType createClassPolyType(ClassRefList classes,
                                           Signature state,
                                           List<? extends NameTypePair> attribute,
                                           List<? extends NameSignaturePair> operation,
                                           ClassRef rootClass)
  {
    ClassPolyType result =
      ozFactory_.createClassPolyType(classes, state, attribute, operation, rootClass);
    return result;
  }

  public ClassUnionType createClassUnionType()
  {
    ClassUnionType result = createClassUnionType();
    return result;
  }

  public ClassUnionType createClassUnionType(ClassRefList classes,
                                             Signature state,
                                             List<? extends NameTypePair> attribute,
                                             List<? extends NameSignaturePair> operation)
  {
    ClassUnionType result =
      ozFactory_.createClassUnionType(classes, state, attribute, operation);
    return result;
  }

  public VariableClassType createVariableClassType()
  {
    return new VariableClassType(this);
  }

  public NameSignaturePair createNameSignaturePair(Name declName,
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
    ClassRefList classes = createClassRefList();
    Signature state = createSignature();
    List<NameTypePair> attrs = list();
    List<NameSignaturePair> ops = list();
    ClassUnionType cuType = createClassUnionType(classes, state, attrs, ops);
    PowerType result = createPowerType(cuType);
    return result;
  }

  public ClassUnionExpr createClassUnionExpr()
  {
    return ozFactory_.createClassUnionExpr();
  }
}
