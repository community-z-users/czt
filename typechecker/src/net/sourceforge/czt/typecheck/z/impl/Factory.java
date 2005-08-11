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
package net.sourceforge.czt.typecheck.z.impl;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.util.ParameterAnn;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
{
  /** The ZFactory that is used to create wrapped types. */
  protected ZFactory zFactory_;

  public Factory()
  {
    zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  }

  public Factory(ZFactory zFactory)
  {
    zFactory_ = zFactory;
  }

  public ZFactory getZFactory()
  {
    return zFactory_;
  }

  public static Term cloneTerm(Term term)
  {
    return cloneTerm(term, term);
  }

  public static Term cloneTerm(Term term, Term rootTerm)
  {
    Object [] children = term.getChildren();
    Object [] args = new Object [children.length];
    for (int i = 0; i < children.length; i++) {
      Object next = children[i];
      if (next == rootTerm) {
        args[i] = next;
      }
      else if (next != null && next instanceof Term) {
        Term nextTerm = (Term) next;
        args[i] = cloneTerm(nextTerm, rootTerm);
      }
      else {
        args[i] = children[i];
      }
    }
    Term result = term.create(args);
    assert result.equals(term);
    copyAnns(term, result);
    return result;
  }

  //copy the LocAnn and TypeEnvAnn from term1 to term2
  public static void copyAnns(Term term1, Term term2)
  {
    if (term1 instanceof TermA && term2 instanceof TermA) {
      TermA termA1 = (TermA) term1;
      TermA termA2 = (TermA) term2;
      LocAnn locAnn = (LocAnn) termA1.getAnn(LocAnn.class);
      if (locAnn != null) {
        termA2.getAnns().add(locAnn);
      }
      UndeclaredAnn uAnn = (UndeclaredAnn) termA1.getAnn(UndeclaredAnn.class);
      if (uAnn != null) {
        termA2.getAnns().add(uAnn);
      }
    }
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

  public NameNamePair createNameNamePair(RefName refName, DeclName declName)
  {
    NameNamePair result = zFactory_.createNameNamePair(refName, declName);
    return result;
  }

  public NameTypePair createNameTypePair(DeclName declName, Type type)
  {
    NameTypePair pair =
      zFactory_.createNameTypePair(declName, type);
    NameTypePair result = new NameTypePairImpl(pair);
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

  public Signature createSignature(List pairs)
  {
    return zFactory_.createSignature(pairs);
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

  public UnknownType createUnknownType(RefName refName)
  {
    return new UnknownType(refName);
  }

  public UnknownType createUnknownType(RefName refName, boolean isMem)
  {
    return new UnknownType(refName, isMem);
  }

  public UnknownType createUnknownType(RefName refName,
                                       boolean isMem,
                                       List<Type2> types)
  {
    return new UnknownType(refName, isMem, types);
  }

  public UnknownType createUnknownType(RefName refName,
                                       boolean isMem,
                                       List<Type2> types,
                                       List<NameNamePair> pairs)
  {
    return new UnknownType(refName, isMem, types, pairs);
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

  public TypeEnvAnn createTypeEnvAnn(List pairs)
  {
    return zFactory_.createTypeEnvAnn(pairs);
  }

  public SectTypeEnvAnn createSectTypeEnvAnn(List nameSecTypeTriple)
  {
    return zFactory_.createSectTypeEnvAnn(nameSecTypeTriple);
  }

  public DeclName createDeclName(String word, List stroke)
  {
    return zFactory_.createDeclName(word, stroke, null);
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

  public RefName createRefName(String word)
  {
    return createRefName(word, list(), null);
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

  public RefExpr createRefExpr(RefName refName)
  {
    return createRefExpr(refName, list(), Boolean.FALSE);
  }

  public RefExpr createRefExpr(RefName refName, List expr, Boolean mixfix)
  {
    return zFactory_.createRefExpr(refName, expr, mixfix);
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

  protected List list()
  {
    return new java.util.ArrayList();
  }
}
