package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * Unifies a variable type with another type.
 */
public class UnificationEnv
{
  protected static final UResult SUCC = UResult.SUCC;
  protected static final UResult PARTIAL = UResult.PARTIAL;
  protected static final UResult FAIL = UResult.FAIL;

  /** A Factory. */
  protected Factory factory_ = null;

  /** The list of generic names and their unified types. */
  protected Stack genUnificationInfo_ = null;

  public UnificationEnv()
  {
    this(new ZFactoryImpl());
  }

  public UnificationEnv(ZFactory zFactory)
  {
    factory_ = new Factory(zFactory);
    genUnificationInfo_ = new Stack();
  }

  public void enterScope()
  {
    List info = list();
    genUnificationInfo_.push(info);
  }

  public void exitScope()
  {
    genUnificationInfo_.pop();
  }

  /**
   * Add a gen name and type to this unificiation
   * environment. Return true iff this name is not in the environment,
   * or its type unifies with the existing type.
   */
  public boolean addGenName(DeclName name, Type2 type2)
  {
    boolean result = false;

    NameTypePair nameTypePair =
      factory_.createNameTypePair(name, type2);
    peek().add(nameTypePair);
    result = true;

    return result;
  }

  public Type2 getType(Name name)
  {
    Type2 result = factory_.createUnknownType();

    //look in the generic name unification list
    for (Iterator iter = peek().iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next instanceof NameTypePair) {
        NameTypePair pair = (NameTypePair) next;

        if (pair.getName().getWord().equals(name.getWord()) &&
            pair.getName().getStroke().equals(name.getStroke())) {
          result = (Type2) pair.getType();
          break;
        }
      }
    }

    return result;
  }

  public static boolean containsVariableType(Type2 type)
  {
    boolean result = false;

    if (isVariableType(type)) {
      VariableType vType = (VariableType) type;
      result = vType.getValue() instanceof VariableType;
    }
    else if (isPowerType(type)) {
      result = containsVariableType(powerType(type).getType());
    }
    else if (isGivenType(type)) {
      result = false;
    }
    else if (isGenParamType(type)) {
      result = false;
    }
    else if (isProdType(type)) {
      List types = prodType(type).getType();
      result = false;
      for (Iterator iter = types.iterator(); iter.hasNext(); ) {
        Type2 nextType = (Type2) iter.next();
        if (containsVariableType(nextType)) {
          result = true;
        }
      }
    }
    else if (isSchemaType(type)) {
      Signature signature = schemaType(type).getSignature();
      result = containsVariableType(signature);
    }

    return result;
  }


  protected static boolean containsVariableType(Signature signature)
  {
    boolean result = false;

    if (signature instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) signature;
      if (vSig.getValue() == vSig) {
        result = true;
      }
      else {
        result = containsVariableType(vSig.getValue());
      }
    }
    else {
      List pairs = signature.getNameTypePair();
      for (Iterator iter = pairs.iterator(); iter.hasNext(); ) {
        NameTypePair pair = (NameTypePair) iter.next();
        if (containsVariableType(unwrapType(pair.getType()))) {
          result = true;
        }
      }
    }

    return result;
  }

  public boolean unifyAux(Type2 typeA, Type2 typeB)
  {
    UResult result = unify(typeA, typeB);
    return !FAIL.equals(result);
  }

  public UResult unify(Type2 typeA, Type2 typeB)
  {
    UResult result = FAIL;

    //if either type is unknown, return PARTIAL
    if (typeA instanceof UnknownType || typeB instanceof UnknownType) {
      result = PARTIAL;
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

  protected UResult unifyVariableType(VariableType vType, Type2 type2)
  {
    UResult result = SUCC;

    //if the types points to the same reference, do nothing, except
    //return PARTIAL if they are both variable types
    if (vType.getValue() == type2) {
      if (type2 instanceof VariableType) {
        result = PARTIAL;
      }
    }
    else {
      if (contains(type2, vType)) {
        result = FAIL;
      }
      else {
        //if the vType is not unified, then unify it with type2
        if (vType.getValue() == vType) {
          vType.setValue(type2);
        }
        result = unify(vType.getValue(), type2);
      }
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

    List typesA = prodTypeA.getType();
    List typesB = prodTypeB.getType();

    //if the size is not equal, fail
    if (typesA.size() == typesB.size()) {
      for (int i = 0; i < typesA.size(); i++) {
        UResult unified =
          unify((Type2) typesA.get(i), (Type2) typesB.get(i));
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

    if (isVariableSignature(sigA)) {
      result = unifyVariableSignature((VariableSignature) sigA, sigB);
    }
    else if (isVariableSignature(sigB)) {
      result = unifyVariableSignature((VariableSignature) sigB, sigA);
    }
    else {
      List listA = sigA.getNameTypePair();
      List listB = sigB.getNameTypePair();
      if (listA.size() == listB.size()) {
        //iterate through every name/type pair, looking for each name in
        //the other signature
        for (Iterator iterA = listA.iterator(); iterA.hasNext(); ) {
          NameTypePair pairA = (NameTypePair) iterA.next();
          NameTypePair pairB = findInSignature(pairA.getName(), sigB);

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
      }
      else {
        result = FAIL;
      }
    }

    return result;
  }

  protected UResult unifyVariableSignature(VariableSignature vSig,
                                           Signature sigB)
  {
    UResult result = SUCC;

    //if this signature is not unified
    if (vSig.getValue() == vSig) {
      if (vSig.getValue() != sigB) {
        vSig.setValue(sigB);
      }
      //the result must be PARTIAL if the signature contains
      //a variable type or variable signature
      if (containsVariableType(sigB)) {
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

  protected boolean contains(Type2 type2, VariableType vType)
  {
    boolean result = false;

    if (type2 == vType) {
      result = true;
    }
    else if (type2 instanceof PowerType) {
      PowerType powerType = (PowerType) type2;
      result = contains(powerType.getType(), vType);
    }
    else if (type2 instanceof ProdType) {
      ProdType prodType = (ProdType) type2;
      List types = prodType.getType();
      for (Iterator iter = types.iterator(); iter.hasNext(); ) {
        Type2 next = (Type2) iter.next();
        if (contains(next, vType)) {
          result = true;
          break;
        }
      }
    }
    else if (type2 instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) type2;
      Signature signature = schemaType.getSignature();
      result = contains(signature, vType);
    }

    return result;
  }

  protected boolean contains(Signature signature, VariableType vType)
  {
    boolean result = false;
    List pairs = signature.getNameTypePair();
    for (Iterator iter = pairs.iterator(); iter.hasNext(); ) {
      NameTypePair pair = (NameTypePair) iter.next();
      if (contains(unwrapType(pair.getType()), vType)) {
        result = true;
        break;
      }
    }

    return result;
  }

  private List peek()
  {
    List result = list();
    if (genUnificationInfo_.size() > 0) {
      result = (List) genUnificationInfo_.peek();
    }
    return result;
  }

  //if this is a generic type, get the type without the parameters. If
  //not a generic type, return the type
  protected static Type2 unwrapType(Type type)
  {
    Type2 result = null;

    if (type instanceof GenericType) {
      if (genericType(type).getOptionalType() != null) {
        result = genericType(type).getOptionalType();
      }
      else {
        result = genericType(type).getType();
      }
    }
    else {
      result = (Type2) type;
    }

    return result;
  }

  //get a name/type pair corresponding with a particular name
  //return null if this name is not in the signature
  protected NameTypePair findInSignature(DeclName declName,
                                         Signature signature)
  {
    NameTypePair result = null;
    List pairs = signature.getNameTypePair();
    for (Iterator iter = pairs.iterator(); iter.hasNext(); ) {
      NameTypePair nameTypePair = (NameTypePair) iter.next();
      if (nameTypePair.getName().equals(declName)) {
        result = nameTypePair;
        break;
      }
    }
    return result;
  }

  private List list()
  {
    return new ArrayList();
  }

  protected static boolean isType2(Type type)
  {
    return (type instanceof Type2);
  }

  protected static boolean isSchemaType(Type type)
  {
    return (type instanceof SchemaType);
  }

  protected static boolean isPowerType(Type type)
  {
    return (type instanceof PowerType);
  }

  protected static boolean isGivenType(Type type)
  {
    return (type instanceof GivenType);
  }

  protected static boolean isGenericType(Type type)
  {
    return (type instanceof GenericType);
  }

  protected static boolean isGenParamType(Type type)
  {
    return (type instanceof GenParamType);
  }

  protected static boolean isProdType(Type type)
  {
    return (type instanceof ProdType);
  }

  protected static boolean isUnknownType(Type type)
  {
    return (type instanceof UnknownType);
  }

  protected static boolean isVariableType(Type type)
  {
    return (type instanceof VariableType);
  }

  protected static boolean isVariableSignature(Signature signature)
  {
    return (signature instanceof VariableSignature);
  }

  //non-safe typecast
  protected static SchemaType schemaType(Type type)
  {
    return (SchemaType) type;
  }

  //non-safe typecast
  protected static PowerType powerType(Type type)
  {
    return (PowerType) type;
  }

  //non-safe typecast
  protected static GivenType givenType(Type type)
  {
    return (GivenType) type;
  }

  //non-safe typecast
  protected static GenericType genericType(Type type)
  {
    return (GenericType) type;
  }

  //non-safe typecast
  protected static GenParamType genParamType(Type type)
  {
    return (GenParamType) type;
  }

  //non-safe typecast
  protected static ProdType prodType(Type type)
  {
    return (ProdType) type;
  }

  //non-safe typecast
  protected static UnknownType unknownType(Type type)
  {
    return (UnknownType) type;
  }

  //non-safe typecast
  protected static VariableType variableType(Type type)
  {
    return (VariableType) type;
  }

  //non-safe typecast
  protected static VariableSignature variableSignature(Signature signature)
  {
    return (VariableSignature) signature;
  }
}
