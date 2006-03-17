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

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.ParameterAnn;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
{
  /** The ZFactory that is used to create wrapped types. */
  protected ZFactory zFactory_;

  /** Used for generating unique ids in names. */
  protected int id_ = 0;

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
    List<Term> listTerm = new java.util.ArrayList();
    listTerm.add(term);
    return cloneTerm(term, listTerm);
  }

  public static Term cloneTerm(Term term, List<Term> listTerm)
  {
    Object [] children = term.getChildren();
    Object [] args = new Object [children.length];
    for (int i = 0; i < children.length; i++) {
      Object next = children[i];
      if (containsObject(listTerm, next)) {
        args[i] = next;
      }
      else if (next != null && next instanceof Term) {
        Term nextTerm = (Term) next;
        args[i] = cloneTerm(nextTerm, listTerm);
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

  public ProdType createProdType(List<Type2> type)
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

  public GenericType createGenericType(List<ZDeclName> zDeclName,
                                       Type2 type,
                                       Type2 optionalType)
  {
    GenericType genericType =
      zFactory_.createGenericType(zDeclName, type, optionalType);
    GenericType result = new GenericTypeImpl(genericType);
    return result;
  }

  public GenParamType createGenParamType(ZDeclName zDeclName)
  {
    return zFactory_.createGenParamType(zDeclName);
  }

  public GivenType createGivenType(ZDeclName zDeclName)
  {
    return zFactory_.createGivenType(zDeclName);
  }

  public NewOldPair createNewOldPair(DeclName declName, RefName refName)
  {
    NewOldPair result = zFactory_.createNewOldPair(declName, refName);
    return result;
  }

  public NewOldPair createNewOldPair(NewOldPair newOldPair)
  {
    DeclName newName = newOldPair.getNewName();
    RefName oldName = newOldPair.getOldName();
    NewOldPair result = createNewOldPair(newName, oldName);
    return result;
  }

  public NameTypePair createNameTypePair(DeclName declName, Type type)
  {
    NameTypePair pair = zFactory_.createNameTypePair(declName, type);
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

  public Signature createSignature(List<NameTypePair> pairs)
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

  public VariableType createVariableType(ZDeclName zDeclName)
  {
    return new VariableType(zDeclName);
  }

  public UnknownType createUnknownType()
  {
    return new UnknownType();
  }

  public UnknownType createUnknownType(ZRefName zRefName)
  {
    return new UnknownType(zRefName);
  }

  public UnknownType createUnknownType(ZRefName zRefName, boolean isMem)
  {
    return new UnknownType(zRefName, isMem);
  }

  public UnknownType createUnknownType(ZRefName zRefName,
                                       boolean isMem,
                                       List<Type2> types)
  {
    return new UnknownType(zRefName, isMem, types);
  }

  public UnknownType createUnknownType(ZRefName zRefName,
                                       boolean isMem,
                                       List<Type2> types,
                                       List<NewOldPair> pairs)
  {
    return new UnknownType(zRefName, isMem, types, pairs);
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

  public TypeEnvAnn createTypeEnvAnn(List<NameTypePair> pairs)
  {
    return zFactory_.createTypeEnvAnn(pairs);
  }

  public SectTypeEnvAnn createSectTypeEnvAnn(List<NameSectTypeTriple> triples)
  {
    return zFactory_.createSectTypeEnvAnn(triples);
  }

  public ZDeclName createZDeclName(String word)
  {
    return createZDeclName(word, this.<Stroke>list());
  }

  public ZDeclName createZDeclName(String word, List<Stroke> stroke)
  {
    return createZDeclName(word, stroke, null);
  }

  public ZDeclName createZDeclName(String word, List<Stroke> stroke, String id)
  {
    ZDeclName result = zFactory_.createZDeclName(word, stroke, id);
    addDeclNameID(result);
    return result;
  }

  public ZDeclName createZDeclName(ZDeclName zDeclName)
  {
    ZDeclName result = zFactory_.createZDeclName(zDeclName.getWord(),
						 zDeclName.getStroke(),
						 zDeclName.getId());
    copyLocAnn(zDeclName, result);
    return result;
  }

  public ZDeclName createZDeclName(ZRefName zRefName)
  {
    ZDeclName result =
       createZDeclName(zRefName.getWord(), zRefName.getStroke(), null);
    copyLocAnn(zRefName, result);
    return result;
  }

  public ZRefName createZRefName(String word)
  {
    return createZRefName(word, this.<Stroke>list(), null);
  }

  public ZRefName createZRefName(String word,
                                 List<Stroke> stroke,
                                 ZDeclName declName)
  {
    return zFactory_.createZRefName(word, stroke, declName);
  }

  public ZRefName createZRefName(ZRefName zRefName)
  {
    ZRefName result =  createZRefName(zRefName.getWord(),
				      zRefName.getStroke(),
				      zRefName.getDecl());
    copyLocAnn(zRefName, result);
    return result;
  }

  public ZRefName createZRefName(ZDeclName zDeclName)
  {
    return createZRefName(zDeclName.getWord(), zDeclName.getStroke(), null);
  }

  public RefExpr createRefExpr(RefName refName)
  {
    return createRefExpr(refName, this.<Expr>list(), Boolean.FALSE);
  }

  public RefExpr createRefExpr(RefName refName,
                               List<Expr> expr,
                               Boolean mixfix)
  {
    ZExprList zExprList = zFactory_.createZExprList(expr);
    return zFactory_.createRefExpr(refName, zExprList, mixfix);
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

  public ZRenameList createZRenameList(List<NewOldPair> pairs)
  {
    return zFactory_.createZRenameList(pairs);
  }

  public void addDeclNameID(DeclName declName)
  {
    if (declName instanceof ZDeclName) {
      ZDeclName zDeclName = (ZDeclName) declName;
      zDeclName.setId(freshId().toString());
    }
  }

  public Integer freshId()
  {
    return new Integer(id_++);
  }

  public void copyLocAnn(TermA src, TermA dest)
  {
    Object locAnn = src.getAnn(LocAnn.class);
    if (locAnn != null) {
      dest.getAnns().add(locAnn);
    }
  }

  public <E> List<E> list()
  {
    java.util.List<E> result = new java.util.ArrayList<E>();
    return result;
  }

  public <E> List<E> list(E... elems)
  {
    java.util.List<E> result = new java.util.ArrayList<E>();
    result.addAll(java.util.Arrays.asList(elems));
    return result;
  }

  public <E> List<E> list(List<E> list)
  {
    List<E> result = new java.util.ArrayList<E>(list);
    return result;
  }
}
