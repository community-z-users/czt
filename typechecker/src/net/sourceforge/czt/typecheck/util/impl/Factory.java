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

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
{
  /** The ZFactory that is used to create wrapped types. */
  protected ZFactory zFactory_;

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

  public ZFactory getZFactory()
  {
    return zFactory_;
  }

  public OzFactory getOzFactory()
  {
    return ozFactory_;
  }

  public PowerType createPowerType()
  {
    VariableType vType = createVariableType();
    PowerType result = createPowerType(vType);
    return result;
  }

  public PowerType createPowerType(Type2 type)
  {
    PowerType powerType = zFactory_.createPowerType(type);
    PowerType result = new PowerTypeImpl(powerType);
    return result;
  }

  public ProdType createProdType(List type)
  {
    ProdType prodType = zFactory_.createProdType(type);
    ProdType result = new ProdTypeImpl(prodType);
    return result;
  }

  public SchemaType createSchemaType()
  {
    VariableSignature vSignature = createVariableSignature();
    SchemaType result = createSchemaType(vSignature);
    return result;
  }

  public SchemaType createSchemaType(Signature signature)
  {
    SchemaType schemaType = zFactory_.createSchemaType(signature);
    SchemaType result = new SchemaTypeImpl(schemaType);
    return result;
  }

  public GenericType createGenericType(List declName,
                                       Type2 type,
                                       Type2 optionalType)
  {
    GenericType genericType =
      zFactory_.createGenericType(declName, type, optionalType);
    GenericType result = new GenericTypeImpl(genericType);
    return result;
  }

  public GenParamType createGenParamType(DeclName declName)
  {
    return zFactory_.createGenParamType(declName);
  }

  public GivenType createGivenType(DeclName declName)
  {
    return zFactory_.createGivenType(declName);
  }

  public NameTypePair createNameTypePair(DeclName declName, Type type)
  {
    NameTypePair nameTypePair =
      zFactory_.createNameTypePair(declName, type);
    NameTypePair result = new NameTypePairImpl(nameTypePair);
    return result;
  }

  public NameSectTypeTriple createNameSectTypeTriple(DeclName declName,
                                                     String section,
                                                     Type type)
  {
    NameSectTypeTriple nameSectTypeTriple =
      zFactory_.createNameSectTypeTriple(declName, section, type);
    NameSectTypeTriple result =
      new NameSectTypeTripleImpl(nameSectTypeTriple);
    return result;
  }

  public Signature createSignature()
  {
    return zFactory_.createSignature();
  }

  public Signature createSignature(List nameTypePair)
  {
    return zFactory_.createSignature(nameTypePair);
  }

  public VariableSignature createVariableSignature()
  {
    return new VariableSignature(this);
  }

  public VariableType createVariableType()
  {
    return new VariableType(this);
  }

  public VariableType createVariableType(DeclName declName)
  {
    return new VariableType(declName);
  }

  public UnknownType createUnknownType()
  {
    return new UnknownType();
  }

  public UnknownType createUnknownType(DeclName declName)
  {
    return new UnknownType(declName);
  }

  public TypeAnn createTypeAnn()
  {
    return zFactory_.createTypeAnn();
  }

  public TypeAnn createTypeAnn(Type type)
  {
    TypeAnn typeAnn = zFactory_.createTypeAnn(type);
    TypeAnn result = new TypeAnnImpl(typeAnn);
    return result;
  }

  public SignatureAnn createSignatureAnn(Signature signature)
  {
    SignatureAnn signatureAnn = zFactory_.createSignatureAnn(signature);
    SignatureAnn result = new SignatureAnnImpl(signatureAnn);
    return result;
  }

  public SectTypeEnvAnn createSectTypeEnvAnn(List nameSecTypeTriple)
  {
    return zFactory_.createSectTypeEnvAnn(nameSecTypeTriple);
  }

  public DeclName createDeclName(String word, List stroke, String id)
  {
    return zFactory_.createDeclName(word, stroke, id);
  }

  public DeclName createDeclName(DeclName declName)
  {
    return createDeclName(declName.getWord(), declName.getStroke(),
                          declName.getId());
  }

  public DeclName createDeclName(RefName refName)
  {
    return createDeclName(refName.getWord(), refName.getStroke(), null);
  }

  public RefName createRefName(String word, List stroke, DeclName declName)
  {
    return zFactory_.createRefName(word, stroke, declName);
  }

  public RefName createRefName(RefName refName)
  {
    return zFactory_.createRefName(refName.getWord(), refName.getStroke(),
                                   refName.getDecl());
  }

  public RefName createRefName(DeclName declName)
  {
    return zFactory_.createRefName(declName.getWord(),
                                   declName.getStroke(),
                                   null);
  }

  public RefExpr createRefExpr(RefName refName, List expr, Boolean mixfix)
  {
    return zFactory_.createRefExpr(refName, expr, mixfix);
  }

  public MuExpr createMuExpr(SchText schText, Expr expr)
  {
    return zFactory_.createMuExpr(schText, expr);
  }

  public TupleExpr createTupleExpr(List expr)
  {
    return zFactory_.createTupleExpr(expr);
  }

  public InStroke createInStroke()
  {
    return zFactory_.createInStroke();
  }

  public OutStroke createOutStroke()
  {
    return zFactory_.createOutStroke();
  }

  public NextStroke createNextStroke()
  {
    return zFactory_.createNextStroke();
  }

  public NumStroke createNumStroke(Integer number)
  {
    return zFactory_.createNumStroke(number);
  }

  public ClassRefType createClassRefType(ClassSig classSig,
                                         ClassRef thisClass,
                                         java.util.List superClass,
                                         VisibilityList visibilityList)
  {
    ClassRefType classRefType =
      ozFactory_.createClassRefType(classSig, thisClass,
                                    superClass, visibilityList);
    ClassRefType result = new ClassRefTypeImpl(classRefType);
    return result;
  }

  public VariableClassSig createVariableClassSig()
  {
    return new VariableClassSig(this);
  }

  public ClassSig createClassSig()
  {
    return ozFactory_.createClassSig();
  }

  public ClassSig createClassSig(List classes,
                                 Signature state,
                                 List attribute,
                                 List operation)
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
    Signature signature = zFactory_.createSignature();
    SchemaType schemaType = zFactory_.createSchemaType(signature);
    PowerType result = zFactory_.createPowerType(schemaType);
    return result;
  }
}
