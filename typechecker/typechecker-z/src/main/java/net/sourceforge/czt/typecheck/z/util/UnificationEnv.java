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
package net.sourceforge.czt.typecheck.z.util;

import java.util.Stack;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.impl.*;

import static net.sourceforge.czt.typecheck.z.util.GlobalDefs.*;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * Provides unification of types.
 */
public class UnificationEnv
{
  protected static final UResult SUCC = UResult.SUCC;
  protected static final UResult PARTIAL = UResult.PARTIAL;
  protected static final UResult FAIL = UResult.FAIL;

  /** A Factory. */
  protected Factory factory_ = null;

  /** The list of generic names and their unified types. */
  protected Stack<List<NameTypePair>> unificationInfo_ = null;

  public UnificationEnv()
  {
    this(new Factory());
  }

  public UnificationEnv(Factory factory)
  {
    factory_ = factory;
    unificationInfo_ = new Stack<List<NameTypePair>>();
  }

  public void enterScope()
  {
    List<NameTypePair> info = factory_.list();
    unificationInfo_.push(info);
  }

  public void exitScope()
  {
    unificationInfo_.pop();
  }

  /**
   * Add a gen name and type to this unificiation  environment.
   */
  public void addGenName(Name name, Type2 type2)
  {
    NameTypePair pair = factory_.createNameTypePair(name, type2);
    peek().add(pair);
  }

  public List<NameTypePair> getPairs()
  {
    List<NameTypePair> result = factory_.list();
    for (List<NameTypePair> pairs : unificationInfo_) {
      result.addAll(pairs);
    }
    return result;
  }

  public Type2 getType(ZName zName)
  {
    Type2 result = factory_.createUnknownType();

    //look in the generic name unification list
    for (NameTypePair pair : peek()) {
      //use "equals" (include the name ID) to counter nested generic
      //environments
      if (zName.equals(pair.getZName())) {
        result = (Type2) pair.getType();
        break;
      }
    }
    return result;
  }

  public boolean containsVariable(Term term)
  {
    return containsVariable(term, factory_.list(term));
  }

  protected boolean containsVariable(Term term, List<Term> preTypes)
  {
    //boolean result = false;

    if (!containsObject(preTypes, term)) {
      preTypes.add(term);
    }

    if (term instanceof VariableType &&
        variableType(term).getValue() == term) {
      return true;
    }
    else if (term instanceof VariableSignature &&
             variableSignature(term).getValue() == term) {
      return true;
    }
    else {
      Object [] children = term.getChildren();
      for (int i = 0; i < children.length; i++) {
        if (children[i] instanceof Term &&
            !containsObject(preTypes, (Term) children[i])) {
          if (containsVariable((Term) children[i], preTypes)) {
            return true;
          }
        }
      }
    }
    return false;
  }

  public UResult strongUnify(Type2 typeA, Type2 typeB)
  {
    return unify(typeA, typeB);
  }

  public UResult unify(Signature sigA, Signature sigB)
  {
    UResult result = unifySignature(sigA, sigB);
    return result;
  }

  public UResult unify(Type2 typeA, Type2 typeB)
  {
    UResult result = FAIL;

    //if the object IDs are the same, there is no need to
    //unify. Variable types are a special case
    if (typeA == typeB && !(typeA instanceof VariableType)) {
      return SUCC;
    }

    //if either type is unknown, return PARTIAL
    if (isUnknownType(typeA)) {
      result = unifyUnknownType(unknownType(typeA), typeB);
    }
    else if (isUnknownType(typeB)) {
      result = unifyUnknownType(unknownType(typeB), typeA);
    }
    else if (isVariableType(typeA)) {
      result = unifyVariableType(variableType(typeA), typeB);
    }
    else if (isVariableType(typeB)) {
      result = unifyVariableType(variableType(typeB), typeA);
    }
    else if (isGivenType(typeA) && isGivenType(typeB)) {
      result = unifyGivenType(givenType(typeA), givenType(typeB));
    }
    else if (isPowerType(typeA) && isPowerType(typeB)) {
      result = unifyPowerType(powerType(typeA), powerType(typeB));
    }
    else if (isProdType(typeA) && isProdType(typeB)) {
      result = unifyProdType(prodType(typeA), prodType(typeB));
    }
    else if (isSchemaType(typeA) && isSchemaType(typeB)) {
      result = unifySchemaType(schemaType(typeA), schemaType(typeB));
    }
    else if (isGenParamType(typeA) && isGenParamType(typeB)) {
      result = unifyGenParamType(genParamType(typeA), genParamType(typeB));
    }

    return result;
  }

  protected UResult unifyUnknownType(UnknownType uType, Type2 type2)
  {
    ZName uTypeName = uType.getZName();
    if (isVariableType(type2) && uTypeName != null) {
      unifyVariableType(variableType(type2), uType);
    }
    else if (isPowerType(type2) &&
             isVariableType(powerType(type2).getType()) &&
             uTypeName != null &&
             uType.getIsMem() == false) {
      UnknownType subType = factory_.createUnknownType(uTypeName, true);
      subType.getType().addAll(uType.getType());
      subType.getPairs().addAll(uType.getPairs());
      unify(powerType(type2).getType(), subType);
    }
    UResult result = PARTIAL;
    return result;
  }

  protected UResult unifyVariableType(VariableType vType, Type2 type2)
  {
    UResult result = SUCC;
    //if this variable is not ground
    if (vType.getValue() == vType) {
      //if we have the same variable, the result is PARTIAL
      if (vType == type2) {
        result = PARTIAL;
      }
      //if type2 contains this variable, then we have a cyclic type, so fail
      else if (contains(type2, vType)) {
        result = FAIL;
      }
      //finally, if everything is ok, assign type2 to the variable
      else {
        vType.setValue(type2);
        result = unify(vType.getValue(), type2);
      }
    }
    //if the variable is already ground, then unify the ground value with type2
    else {
      result = unify(vType.getValue(), type2);
    }
    return result;
  }

  protected UResult unifyGivenType(GivenType givenTypeA, GivenType givenTypeB)
  {
    UResult result = givenTypeA.equals(givenTypeB) ? SUCC : FAIL;
    return result;
  }

  protected UResult unifyPowerType(PowerType powerTypeA, PowerType powerTypeB)
  {
    //try to unify the inner types
    UResult result = unify(powerTypeA.getType(), powerTypeB.getType());
    return result;
  }

  protected UResult unifyProdType(ProdType prodTypeA, ProdType prodTypeB)
  {
    UResult result = SUCC;

    List<Type2> typesA = prodTypeA.getType();
    List<Type2> typesB = prodTypeB.getType();

    //if the size is not equal, fail
    assert typesA.size() > 1;
    assert typesB.size() > 1;
    if (typesA.size() == typesB.size()) {
      for (int i = 0; i < typesA.size(); i++) {
        UResult unified = unify(typesA.get(i), typesB.get(i));
        if (FAIL.equals(unified)) {
          result = FAIL;
        }
        else if (PARTIAL.equals(unified) && !FAIL.equals(result)) {
          result = PARTIAL;
        }
      }
    }
    else {
      result = FAIL;
    }

    return result;
  }

  protected UResult unifyGenParamType(GenParamType genParamTypeA,
                                      GenParamType genParamTypeB)
  {
    UResult result = genParamTypeA.equals(genParamTypeB) ? SUCC : FAIL;
    return result;
  }

  protected UResult unifySchemaType(SchemaType schemaTypeA,
                                    SchemaType schemaTypeB)
  {
    //try to unify the two signatures
    Signature sigA = schemaTypeA.getSignature();
    Signature sigB = schemaTypeB.getSignature();
    UResult result = unifySignature(sigA, sigB);
    return result;
  }

  //unify 2 signatures
  protected UResult unifySignature(Signature sigA, Signature sigB)
  {
    UResult result = SUCC;

    if (sigA == sigB) {
      return SUCC;
    }

    if (isVariableSignature(sigA)) {
      result = unifyVariableSignature((VariableSignature) sigA, sigB);
    }
    else if (isVariableSignature(sigB)) {
      result = unifyVariableSignature((VariableSignature) sigB, sigA);
    }
    else {
      result = unifyResolvedSignature(sigA, sigB);
    }
    return result;
  }

  // for signatures without variable types
  protected UResult unifyResolvedSignature(Signature sigA, Signature sigB)
  {
    Map<String, NameTypePair> mapA = factory_.hashMap();
    Map<String, NameTypePair> mapB = factory_.hashMap();
    for (NameTypePair pair : sigA.getNameTypePair()) {
      //mapA.put(pair.getZName().toString(), pair);
      mapA.put(ZUtils.toStringZName(pair.getZName()), pair);
    }
    for (NameTypePair pair : sigB.getNameTypePair()) {
      //mapB.put(pair.getZName().toString(), pair);
      mapB.put(ZUtils.toStringZName(pair.getZName()), pair);
    }

    UResult resultA = unifySignatureAux(mapA, mapB);
    UResult resultB = unifySignatureAux(mapB, mapA);
    UResult result = UResult.conj(resultA, resultB);
    return result;
  }

  //unify the signature "one-way". Use hashmaps for efficiency
  protected UResult unifySignatureAux(Map<String, NameTypePair> mapA,
                                      Map<String, NameTypePair> mapB)
  {
    UResult result = SUCC;
    Set<Map.Entry<String, NameTypePair>> entrySet = mapA.entrySet();
    for (Map.Entry<String, NameTypePair> first : entrySet) {
      NameTypePair second = mapB.get(first.getKey());
      if (second == null) {
        result = FAIL;
      }
      else {
        UResult unified = unify(unwrapType(first.getValue().getType()),
                                unwrapType(second.getType()));
        if (unified == FAIL) {
          result = FAIL;
        }
        else if (unified == PARTIAL && result != FAIL) {
          result = PARTIAL;
        }
      }
    }
    return result;
  }

  //unify the signature "one-way"
  /*
  protected UResult unifySignatureAux(Signature sigA, Signature sigB)
  {
    UResult result = SUCC;
    List<NameTypePair> listA = sigA.getNameTypePair();
    List<NameTypePair> listB = sigB.getNameTypePair();

    //iterate through every name/type pair, looking for each name in
    //the other signature
    for (int i = 0; i < listA.size(); i++) {
      NameTypePair pairA = listA.get(i);
      NameTypePair pairB = findNameTypePair(pairA.getZName(), sigB);
      //NameTypePair pairB = listB.get(i);
      //if the pair in not in the signature, then fail
      if (pairB == null) {
        result = FAIL;
      }
      else {
        UResult unified = unify(unwrapType(pairA.getType()),
                                unwrapType(pairB.getType()));
        if (unified == FAIL) {
          result = FAIL;
        }
        else if (unified == PARTIAL && result != FAIL) {
          result = PARTIAL;
        }
      }
    }
    return result;
  }
  */

  protected UResult unifyVariableSignature(VariableSignature vSig,
                                           Signature sigB)
  {
    UResult result = SUCC;
    //if this signature is not unified
    if (vSig.getValue() == vSig) {
      //if we have the same variable, the result is PARTIAL
      if (vSig == sigB) {
        result = PARTIAL;
      }
      //if sigB contains this variable, then we have a cyclic type, so fail
      else if (contains(sigB, vSig)) {
        result = FAIL;
      }
      else {
        vSig.setValue(sigB);
        //the result must be PARTIAL if the signature contains
        //a variable type or variable signature
        result = PARTIAL;
      }

    }
    //if the signature is unified, check that the unified value unifies
    //with sigB
    else {
      result = unifySignature(vSig.getValue(), sigB);
    }
    return result;
  }

  //return true if and only if term contains the object o
  protected boolean contains(Term term, Object o)
  {
    boolean result = contains(term, o, factory_.list(term));
    return result;
  }

  protected boolean contains(Term term, Object o, List<Term> preTerms)
  {
    boolean result = false;

    //if this term is the same as the object, then it contains the object
    if (term == o) {
      result = true;
    }
    //otherwise, search the children of this term
    else {
      Object [] children = term.getChildren();
      for (int i = 0; i < children.length; i++) {
        if (children[i] instanceof Term &&
            !containsObject(preTerms, children[i])) {
          if (contains((Term) children[i], o, preTerms)) {
            result = true;
            break;
          }
        }
      }
    }
    return result;
  }

  private List<NameTypePair> peek()
  {
    List<NameTypePair> result = factory_.list();
    if (unificationInfo_.size() > 0) {
      result = unificationInfo_.peek();
    }
    return result;
  }

  protected static boolean isType2(Term term)
  {
    return (term instanceof Type2);
  }

  protected static boolean isSchemaType(Term term)
  {
    return (term instanceof SchemaType);
  }

  protected static boolean isPowerType(Term term)
  {
    return (term instanceof PowerType);
  }

  protected static boolean isGivenType(Term term)
  {
    return (term instanceof GivenType);
  }

  protected static boolean isGenericType(Term term)
  {
    return (term instanceof GenericType);
  }

  protected static boolean isGenParamType(Term term)
  {
    return (term instanceof GenParamType);
  }

  protected static boolean isProdType(Term term)
  {
    return (term instanceof ProdType);
  }

  protected static boolean isUnknownType(Term term)
  {
    return (term instanceof UnknownType);
  }

  protected static boolean isVariableType(Term term)
  {
    return (term instanceof VariableType);
  }

  protected static boolean isVariableSignature(Term term)
  {
    return (term instanceof VariableSignature);
  }

  //non-safe typecast
  protected static SchemaType schemaType(Term term)
  {
    return (SchemaType) term;
  }

  //non-safe typecast
  protected static PowerType powerType(Term term)
  {
    return (PowerType) term;
  }

  //non-safe typecast
  protected static GivenType givenType(Term term)
  {
    return (GivenType) term;
  }

  //non-safe typecast
  protected static GenericType genericType(Term term)
  {
    return (GenericType) term;
  }

  //non-safe typecast
  protected static GenParamType genParamType(Term term)
  {
    return (GenParamType) term;
  }

  //non-safe typecast
  protected static ProdType prodType(Term term)
  {
    return (ProdType) term;
  }

  //non-safe typecast
  protected static UnknownType unknownType(Term term)
  {
    return (UnknownType) term;
  }

  //non-safe typecast
  protected static VariableType variableType(Term term)
  {
    return (VariableType) term;
  }

  //non-safe typecast
  protected static VariableSignature variableSignature(Term term)
  {
    return (VariableSignature) term;
  }

  protected void debug(Object o1, Object o2)
  {
    System.err.println("unify(" + o1 + ", " + o2 + ")");
  }
}
