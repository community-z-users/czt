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

import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;

import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
{
  /** Used for generating unique ids in names. */
  static protected int id_ = 0;

  /** The ZFactory that is used to create wrapped types. */
  protected ZFactory zFactory_;
  protected net.sourceforge.czt.z.util.Factory factory_;
  private Map<String,List<ZName>> ids_ = new HashMap<String,List<ZName>>();

  public Factory()
  {
    zFactory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    factory_ = new net.sourceforge.czt.z.util.Factory(zFactory_);
  }

  public Factory(ZFactory zFactory)
  {
    zFactory_ = zFactory;
    factory_ = new net.sourceforge.czt.z.util.Factory(zFactory_);
  }

  public ZFactory getZFactory()
  {
    return zFactory_;
  }

  public static Term cloneTerm(Term term)
  {
    List<Term> listTerm = new ArrayList<Term>();
    listTerm.add(term);
    return cloneTerm(term, listTerm);
  }

  public static Term cloneTerm(Term term, List<Term> listTerm)
  {
    Object[] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      Object child = children[i];
      if (child instanceof Term &&
          ! containsObject(listTerm, child)) {
        children[i] = cloneTerm((Term) child, listTerm);
      }
    }
    Term result = term.create(children);
    assert result.equals(term);
    copyAnns(term, result);
    return result;
  }

  //copy the LocAnn and UndeclaredAnn from term1 to term2
  public static void copyAnns(Term term1, Term term2)
  {
    LocAnn locAnn = (LocAnn) term1.getAnn(LocAnn.class);
    if (locAnn != null) {
      term2.getAnns().add(locAnn);
    }
    UndeclaredAnn uAnn = (UndeclaredAnn) term1.getAnn(UndeclaredAnn.class);
    if (uAnn != null) {
      term2.getAnns().add(uAnn);
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
    PowerType powerType = factory_.createPowerType(type);
    PowerType result = new PowerTypeImpl(powerType);
    return result;
  }

  public ProdType createProdType(List<Type2> type)
  {
    ProdType prodType = factory_.createProdType(type);
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
    SchemaType schemaType = factory_.createSchemaType(signature);
    SchemaType result = new SchemaTypeImpl(schemaType);
    return result;
  }

  public GenericType createGenericType(NameList nameList,
                                       Type2 type,
                                       Type2 optionalType)
  {
    GenericType genericType =
      factory_.createGenericType(nameList, type, optionalType);
    GenericType result = new GenericTypeImpl(genericType);
    return result;
  }

  public GenericType createGenericType(List<ZName> nameList,
                                       Type2 type,
                                       Type2 optionalType)
  {
    ZNameList list = factory_.createZNameList(nameList);
    return createGenericType(list, type, optionalType);
  }

  public GenParamType createGenParamType(ZName zDeclName)
  {
    return factory_.createGenParamType(zDeclName);
  }

  public GivenType createGivenType(ZName zDeclName)
  {
    return factory_.createGivenType(zDeclName);
  }

  public NewOldPair createNewOldPair(Name declName, Name refName)
  {
    NewOldPair result = factory_.createNewOldPair(declName, refName);
    return result;
  }

  public NewOldPair createNewOldPair(NewOldPair newOldPair)
  {
    Name newName = newOldPair.getNewName();
    Name oldName = newOldPair.getOldName();
    NewOldPair result = createNewOldPair(newName, oldName);
    return result;
  }

  public NameTypePair createNameTypePair(Name declName, Type type)
  {
    NameTypePair pair = factory_.createNameTypePair(declName, type);
    NameTypePair result = new NameTypePairImpl(pair);
    return result;
  }

  public NameSectTypeTriple createNameSectTypeTriple(Name declName,
                                                     String section,
                                                     Type type)
  {
    NameSectTypeTriple nameSectTypeTriple =
      factory_.createNameSectTypeTriple(declName, section, type);
    NameSectTypeTriple result =
      new NameSectTypeTripleImpl(nameSectTypeTriple);
    return result;
  }

  public Signature createSignature()
  {
    return factory_.createSignature();
  }

  public Signature createSignature(List<NameTypePair> pairs)
  {
    return factory_.createSignature(pairs);
  }

  public VariableSignature createVariableSignature()
  {
    return new VariableSignature(this);
  }

  public VariableType createVariableType()
  {
    return new VariableType(this);
  }

  public VariableType createVariableType(ZName zDeclName)
  {
    return new VariableType(zDeclName);
  }

  public UnknownType createUnknownType()
  {
    return new UnknownType();
  }

  public UnknownType createUnknownType(ZName zRefName)
  {
    return new UnknownType(zRefName);
  }

  public UnknownType createUnknownType(ZName zRefName, boolean isMem)
  {
    return new UnknownType(zRefName, isMem);
  }

  public UnknownType createUnknownType(ZName zRefName,
                                       boolean isMem,
                                       List<Type2> types)
  {
    return new UnknownType(zRefName, isMem, types);
  }

  public UnknownType createUnknownType(ZName zRefName,
                                       boolean isMem,
                                       List<Type2> types,
                                       List<NewOldPair> pairs)
  {
    return new UnknownType(zRefName, isMem, types, pairs);
  }

  public TypeAnn createTypeAnn()
  {
    return factory_.createTypeAnn();
  }

  public TypeAnn createTypeAnn(Type type)
  {
    TypeAnn typeAnn = factory_.createTypeAnn(type);
    TypeAnn result = new TypeAnnImpl(typeAnn);
    return result;
  }

  public SignatureAnn createSignatureAnn(Signature signature)
  {
    SignatureAnn signatureAnn = factory_.createSignatureAnn(signature);
    SignatureAnn result = new SignatureAnnImpl(signatureAnn);
    return result;
  }

  public SectTypeEnvAnn createSectTypeEnvAnn(List<NameSectTypeTriple> triples)
  {
    return factory_.createSectTypeEnvAnn(triples);
  }

  public ZStrokeList createZStrokeList(ZStrokeList zStrokeList)
  {
    return factory_.createZStrokeList(zStrokeList);
  }

  public ZName createZDeclName(String word)
  {
    return createZDeclName(word, factory_.createZStrokeList());
  }

  public ZName createZDeclName(String word, StrokeList strokes)
  {
    ZName result = factory_.createZName(word, strokes);
    addNameID(result);
    return result;
  }

  public ZName createZName(ZName zName, boolean copyId)
  {
    ZStrokeList strokes = factory_.createZStrokeList();
    strokes.addAll(zName.getZStrokeList());
    ZName result = factory_.createZName(zName.getWord(), strokes);
    if (copyId) setId(result, zName.getId());
    copyLocAnn(zName, result);
    return result;
  }

  public ZName createZName(String word)
  {
    return createZName(word, factory_.createZStrokeList());
  }

  public ZName createZName(String word, StrokeList strokes)
  {
    return factory_.createZName(word, strokes);
  }

  public ZNameList createZNameList(List<? extends Name> list)
  {
    return factory_.createZNameList(list);
  }

  public RefExpr createRefExpr(Name refName)
  {
    return createRefExpr(refName, this.<Expr>list(), Boolean.FALSE);
  }

  public RefExpr createRefExpr(Name refName,
                               List<Expr> expr,
                               Boolean mixfix)
  {
    ZExprList zExprList = factory_.createZExprList(expr);
    return factory_.createRefExpr(refName, zExprList, mixfix);
  }

  public InStroke createInStroke()
  {
    return factory_.createInStroke();
  }

  public OutStroke createOutStroke()
  {
    return factory_.createOutStroke();
  }

  public NextStroke createNextStroke()
  {
    return factory_.createNextStroke();
  }

  public NumStroke createNumStroke(Integer number)
  {
    return factory_.createNumStroke(number);
  }

  public ZRenameList createZRenameList(List<NewOldPair> pairs)
  {
    return factory_.createZRenameList(pairs);
  }

  public void addNameID(Name declName)
  {
    if (declName instanceof ZName) {
      ZName zName = (ZName) declName;
      if (zName.getId() == null) {
        overwriteNameID(declName);
      }
    }
  }

  public void overwriteNameID(Name declName)
  {
    if (declName instanceof ZName) {
      ZName zName = (ZName) declName;
      String id = freshId().toString();
      String oldId = zName.getId();
      updateIds(oldId, id);
      setId(zName, id);
    }
  }

  public Integer freshId()
  {
    return new Integer(id_++);
  }

  public void merge(ZName name1, ZName name2)
  {
    if (name1.getId() == null && name2.getId() == null) return;
    if (name1.getId() != null && name1.getId().equals(name2.getId())) return;
    String newId = name2.getId();
    String oldId = name1.getId();
    updateIds(oldId, newId);
    setId(name1, newId);
  }

  public void updateIds(String oldId, String newId)
  {
    List<ZName> list = ids_.get(oldId);
    if (list != null) {
      for (ZName zName : list) {
        setId(zName, newId);
      }
      ids_.remove(oldId);
    }
  }

  public void setId(ZName zName, String id)
  {
    zName.setId(id);
    if (id != null) {
      List<ZName> list = ids_.get(id);
      if (list == null) {
        list = list();
      }
      list.add(zName);
      ids_.put(id, list);
    }
  }

  public void copyLocAnn(Term src, Term dest)
  {
    Object locAnn = src.getAnn(LocAnn.class);
    if (locAnn != null) {
      dest.getAnns().add(locAnn);
    }
  }

  public <E> List<E> list()
  {
    java.util.List<E> result = new ArrayList<E>();
    return result;
  }

  public <E> List<E> list(E... elems)
  {
    java.util.List<E> result = new ArrayList<E>();
    result.addAll(java.util.Arrays.asList(elems));
    return result;
  }

  public <E> List<E> list(List<E> list)
  {
    List<E> result = new ArrayList<E>(list);
    return result;
  }

  public <E> ListTerm<E> listTerm()
  {
    ListTerm<E> result = new ListTermImpl<E>();
    return result;
  }

  public <E> ListTerm<E> listTerm(E... elems)
  {
    ListTerm<E> result = listTerm();
    result.addAll(java.util.Arrays.asList(elems));
    return result;
  }

  public <K, V> Map<K, V> hashMap()
  {
    Map<K, V> result = new java.util.HashMap<K, V>();
    return result;
  }
  
  public <V> Set<V> hashSet()
  {
    return new java.util.HashSet<V>();
  }
}
