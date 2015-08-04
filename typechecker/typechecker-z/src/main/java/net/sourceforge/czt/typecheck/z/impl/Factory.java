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
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.util.UndeclaredAnn;

/**
 * A factory for creating types that hide VariableTypes.
 */
public class Factory
{
  /** Used for generating unique ids in names. */
  // TODO: CHECK: made it a long in case of large specs?
  static int id_ = 0;

  /** The ZFactory that is used to create wrapped types. */
  protected ZFactory zFactory_;
  protected net.sourceforge.czt.z.util.Factory factory_;
  
  /** 
   * ZName ids database: each (unique) id has a list of ZName instances associated with it.
   *
   * TODO: CHECK: (ask Tim) 
   * An invariant for the database is that, although the list of names associated with
   * each id refers to different ZName instances, their internal name (i.e. getWord())
   * must be the same.
   */
  private Map<String,List<ZName>> ids_ = new HashMap<String,List<ZName>>();

  public Factory()
  {
    this(new net.sourceforge.czt.z.impl.ZFactoryImpl());     
  }

  public Factory(ZFactory zFactory)
  {
    this(zFactory, new net.sourceforge.czt.z.util.Factory(zFactory));
  }
  
  /**
   * This constructor allows one to give a different util.Factory class,
   * which will allow different extension factories to create the Z objects.
   * @param zFactory
   * @param factory
   */
  public Factory(ZFactory zFactory, net.sourceforge.czt.z.util.Factory factory)
  {
    zFactory_ = zFactory;
    factory_ = factory;
  }
  
  public ZFactory getZFactory()
  {
    return zFactory_;
  }
  
  /**
   * calls cloneTerm with an empty list of ....
   * @param term
   * @return
   */
  public static Term cloneTerm(Term term)
  {
    List<Term> listTerm = new ArrayList<Term>();
    listTerm.add(term);
    return cloneTerm(term, listTerm);
  }

  /**
   * Clones the given term 
   * @param term
   * @param listTerm
   * @return
   */
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
    children = null;
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
    List<Type2> types = new ArrayList<Type2>(optionalType != null ? 2 : 1);
    types.add(type);
    if (optionalType != null) types.add(optionalType);
    GenericType genericType =
      factory_.createGenericType(nameList, types);
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

  public ZStrokeList createZStrokeList()
  {
    return factory_.createZStrokeList();
  }

  public ZStrokeList createZStrokeList(List<? extends Stroke> strokes)
  {
    return factory_.createZStrokeList(strokes);
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

  public ZParaList createZParaList()
  {
    return factory_.createZParaList();
  }

  public ZParaList createZParaList(List<Para> paras)
  {
    return factory_.createZParaList(paras);
  }

  public ZSect createZSect(String name, java.util.List<? extends Parent>
			   parent, ParaList paraList)
  {
    return factory_.createZSect(name, parent, paraList);
  }

  /**
   * <p>
   * Add a name id to the given name if it is a ZName without 
   * an ID already associated with it (see {@link #overwriteNameID(Name)}).
   * Thus, changes are made only if the name does not have an id 
   * associated with it (i.e., it is not a name declaration).
   * </p>
   * <p>
   * In Z, that is always the case for given sets (GivenPara), 
   * free types (FreePara, and FreeType), schemas, and abbreviations 
   * (ConstDecl within AxPara), since they are always declaring names.       
   * </p>
   * <p>
   * Names are also declared for generic type parameters, renaming expressions 
   * (RenameExpr) (i.e. the new names in S[new/old] are declared), and variable 
   * declaraions (VarDecl). 
   * </p>
   * <p>
   * There a few special cases, where name IDs are added, but they do not come
   * directly from the user's specification (see {@link #createZDeclName(String, StrokeList)}). 
   * For instance, variable types/signatures containing unresolved generic types
   * also declare the Z Std alpha/beta variables used during generic type inference.
   * Other places where this occurs are decoration expressions (i.e. schema decoration),
   * and the merged signature for schema composition and piping.
   * </p>
   */ 
  // TODO: CHECK: createZDeclName/addNameID is also used within createCompSig and createCompPipe of
  //              of ExprChecker to check singature compatibility within such expressiongs
  public void addNameID(Name declName)
  {
    if (declName instanceof ZName) {
      ZName zName = (ZName) declName;
      if (zName.getId() == null) {
        overwriteNameID(declName);
      }
    }
  }

  /**
   * <p>
   * When the name being declared is a ZName, a fresh unique id 
   * is generated and associated for declName, and the old id is
   * updated for this name within the id database maintained by 
   * this factory (see {@link #updateIds(String, String) updateIds}).
   * </p>
   * <p>
   * This special method is usually called by {@link #addNameID(Name) addNameID}.
   * One exception is typechecking of schema references within the ExprChecker 
   * RefExpr. In that case, if the referred schema signature already had its
   * generic types resolved (i.e. it isn't a VariableSignature), then new names
   * are created and their ids overwritten. As in this name copying process the
   * old name ids are ``forgotten'', overriting in fact just 
   * {@link #updateIds(String, String) updateIds} with the uniquely created one.
   * </p>
   */     
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
  
  /**
   * <p>
   * Merge the ids from the two names given. That is, the method does nothing
   * if the IDs are either both null or equal. Otherwise, the id of the newName
   * is set for the oldName, and the id database for the oldName id is also updated.
   * </p>
   * <p>
   * This is important in the case whilst checking duplicate names that may appear
   * in different scopes. If the duplication is valid (e.g.,), the ids are merged 
   * and the first name occurring id (newName id) is updated in the database.
   * Otherwise, if duplication isn't valid, the update takes place as well, but an
   * error should be added (see 
   * {@link net.sourceforge.czt.typecheck.z.Checker#checkForDuplicates(List<NameTypePair>,
        List<Term>, String)}.)
   * </p>
   */   
  public void merge(ZName oldName, ZName newName)
  {
    if (oldName.getId() == null && newName.getId() == null) return;
    if (oldName.getId() != null && oldName.getId().equals(newName.getId())) return;
    String newId = newName.getId();
    String oldId = oldName.getId();
    updateIds(oldId, newId);
    setId(oldName, newId);
  }
  
  private static synchronized void incrementId()
  {
	  id_++;
  }

  /**
   * Creates a fresh ID seed to be used for unique ids.
   */
  protected Integer freshId()
  {
    Integer result = Integer.valueOf(id_);
    incrementId();
    return result;
  }

  /**
   * Update the id database of names for oldId by associating all such names
   * with the newId given (see {@link #setId(ZName, String) setId}). If oldId 
   * is itself unknown (or null), then no update is performed.
   */     
  // NOTE: as the IDs database is within the factory, we (Leo) changed 
  //       this method from public to protected. This way, only through
  //       the appropriate factory method it is possible update the ids DB.
  protected void updateIds(String oldId, String newId)
  {
    List<ZName> list = ids_.get(oldId);
    if (list != null) {
      for (ZName zName : list) {
        setId(zName, newId);
      }
      ids_.remove(oldId);
    }
  }

  /**
   * Associate the given id to given name (see {@link ZName#setId(String)}).
   * If the id is non-null, the id database is also updated. That is, 
   * either a new list of names is associated with the id in case it is 
   * new to the database; otherwise, the given name is added to the list
   * of names associated with this id.
   */
  protected void setId(ZName zName, String id)
  {     
    zName.setId(id);
    if (id != null) {
      List<ZName> list = ids_.get(id);
      if (list == null) {
        list = list();
      }
      
      // check the name ID DB consistency (put to a method to allow room for "special" cases)
      assert checkNameIDDBInvariant(zName, list);
      
      list.add(zName);
      ids_.put(id, list);
    }
  }
  
  /**
   * Checks the id DB invariant that names within the mapped list for the 
   * given zName.getId() must the same getWord() result.
   */
  protected boolean checkNameIDDBInvariant(ZName zName, List<ZName> list)
  {
    assert zName != null && list != null;
    //do not consider the "deltaxi" special case, though
    
    // Name ID database invariant: getWord() equality among mapped names.
    // zName.getId() != null && !list.isEmpty() ==> zName.getWord().equals(list.get(0).getWord())
    // 
    // TODO: CHECK: 
    // Strokes are NOT taken into account (i.e., GlobalDefs.namesEqual(zName, list.get(0)); why not?)
    boolean result = (zName.getId() == null || list.isEmpty() || zName.getId().equals("deltaxi")) || 
      zName.getWord().equals(list.get(0).getWord()); 
      //namesEqual(zName, list.get(0));   
    assert result : 
      "Typechecker name id database invariant broken for id " + 
      String.valueOf(zName.getId()) +
      ". The given name " + String.valueOf(zName) + " getWord() result differ from " +
      "other names associated with the same id (e.g., " + 
      (list.isEmpty() ? "--" : String.valueOf(list.get(0))) +
      ", id " + list.get(0).getId() + 
          (list.get(0).getZStrokeList().isEmpty() ? "" : 
            ", storkes " +  list.get(0).getZStrokeList().get(0).getClass()) 
      + "). " +  "This is a serious error and should never happen.";
    return result;
  }
  
  /**
   * <p>
   * In Z, Delta/Xi names are a special case of declared names (i.e. \Delta S)
   * that have peculiar ID:~they may not yet have (e.g., at first occurrence)
   * any corresponding ZName associated with them. So if there is not,
   * we add a fixed (global) id.
   * </p>
   * <p>
   * Other extensions requiring similar features
   * should extend their corresponding typechecker factory accordingly.
   * </p>
   */
  public void setDeltaXiID(ZName zName)
  {
     setId(zName, "deltaxi");
  }
     
  public <E> List<E> list()
  {
    java.util.List<E> result = new ArrayList<E>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    return result;
  }

  public <E> List<E> list(@SuppressWarnings("unchecked") E... elems)
  {
	java.util.List<E> result = new ArrayList<E>(elems.length + PerformanceSettings.INITIAL_ARRAY_CAPACITY);
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

  public <E> ListTerm<E> listTerm(@SuppressWarnings("unchecked") E... elems)
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
