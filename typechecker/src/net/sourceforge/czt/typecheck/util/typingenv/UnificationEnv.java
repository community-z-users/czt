package net.sourceforge.czt.typecheck.util.typingenv;

import java.io.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.typecheck.z.*;

/**
 * Unifies a variable type with an actual type.
 */
public class UnificationEnv
{
  /** A ZFactory. */
  protected ZFactory factory_ = null;

  /** The list of generic names and their unified types. */
  protected Stack genUnificationInfo_ = null;

  /** The list of variable types and their names. */
  protected List varUnificationInfo_ = null;

  public UnificationEnv()
  {
    factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    genUnificationInfo_ = new Stack();
    varUnificationInfo_ = new ArrayList();
  }

  public void dump()
  {
    System.err.println("*********************");
    for (Iterator iter = varUnificationInfo_.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next instanceof NameTypePair) {
        NameTypePair pair = (NameTypePair) next;
        System.err.println(pair.getName() + " : " + pair.getType());
      }
      else if (next instanceof NameSignaturePair) {
        NameSignaturePair pair = (NameSignaturePair) next;
        System.err.println(pair.getName() + " : " + pair.getSignature());
      }
      else {
        System.err.println("type = " + next.getClass().getName());
      }
    }
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

    if (unifies(name, type2)) {
      NameTypePair nameTypePair =
        factory_.createNameTypePair(name, type2);
      peek().add(nameTypePair);
      result = true;
    }

    return result;
  }

  /**
   * Add a variable type name and type to this environment.
   */
  public void addVarName(DeclName name, Type2 type2)
  {
    NameTypePair nameTypePair = factory_.createNameTypePair(name, type2);
    varUnificationInfo_.add(nameTypePair);
  }

  /**
   * Add the name and sig to this unificiation
   * environment.
   */
  public void addVarSigName(DeclName name, Signature signature)
  {
    NameSignaturePair nameSignaturePair =
      new NameSignaturePair(name, signature);
    varUnificationInfo_.add(nameSignaturePair);
  }

  /**
   * Returns true if and only if the name is in this unification env.
   */
  public boolean contains(Name name)
  {
    boolean result = false;

    for (Iterator iter = varUnificationInfo_.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next instanceof NameTypePair) {
        NameTypePair pair = (NameTypePair) next;

        if (pair.getName().getWord().equals(name.getWord()) &&
            pair.getName().getStroke().equals(name.getStroke())) {
          result = true;
        }
      }
    }

    return result;
  }

  public Type2 getType(Name name)
  {
    Type2 result = UnknownTypeImpl.create();

    //first look in the generic name unification list
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

    //if not in the gen list, try the variable list
    if (result instanceof UnknownType) {
      for (Iterator iter = varUnificationInfo_.iterator(); iter.hasNext(); ) {
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
    }

    if (result instanceof VariableType &&
        !name.equals(variableType(result).getName())) {
      VariableType variableType = (VariableType) result;
      Type2 recursiveResult = getType(variableType.getName());
      if (! (recursiveResult instanceof UnknownType)) {
        result = recursiveResult;
      }
    }

    return result;
  }

  public Signature getSignature(Name name)
  {
    Signature result = null;

    for (Iterator iter = varUnificationInfo_.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next instanceof NameSignaturePair) {
        NameSignaturePair pair = (NameSignaturePair) next;

        if (pair.getName().getWord().equals(name.getWord()) &&
            pair.getName().getStroke().equals(name.getStroke())) {
          result = pair.getSignature();
          break;
        }
      }
    }

    return result;
  }

  public boolean unify(Type2 typeA, Type2 typeB)
  {
    boolean unified = false;

    //first check for the special case of where the two references
    //point to the same object
    if (typeA == typeB) {
      return true;
    }

    if (isVariableType(typeA)) {
      unified = unifyVariableType(variableType(typeA), typeB);
    }
    else if (isVariableType(typeB)) {
      unified = unifyVariableType(variableType(typeB), typeA);
    }
    else if (isGivenType(typeA) && isGivenType(typeB)) {
      unified = unifyGivenType(givenType(typeA), givenType(typeB));
    }
    else if (isPowerType(typeA) && isPowerType(typeB)) {
      unified = unifyPowerType(powerType(typeA), powerType(typeB));
    }
    else if (isProdType(typeA) && isProdType(typeB)) {
      unified = unifyProdType(prodType(typeA), prodType(typeB));
    }
    else if (isSchemaType(typeA) && isSchemaType(typeB)) {
      unified = unifySchemaType(schemaType(typeA), schemaType(typeB));
    }
    else if (isGenParamType(typeA) && isGenParamType(typeB)) {
      unified = unifyGenParamType(genParamType(typeA), genParamType(typeB));
    }

    return unified;
  }

  /*
  protected Type2 unifyVariableType(VariableType variableType, Type2 type2)
  {
    Type2 result = null;

    //try to find the type in the unification environment
    Type2 possibleType = getType(variableType.getName());
    if (!isUnknownType(possibleType)) {
      if (possibleType.equals(variableType)) {
        result = type2;
      }
      else {
        result = unify((Type2) possibleType, type2);
      }
    }
    else if (!isUnknownType(type2)) {
      //if type2 is also a variable, merge the dependent list
      if (isVariableType(type2)) {
        variableType(type2).getDependent().addAll(variableType.getDependent());
      }

      //let the dependents know of the change
      List dependents = variableType.getDependent();
      for (Iterator iter = dependents.iterator(); iter.hasNext(); ) {
        Object next = iter.next();
        updateType(next, variableType, type2);
      }

      addVarName(variableType.getName(), type2);
      result = type2;
    }
    else {
      result = variableType;
    }

    return result;
  }

  protected Type2 unifyGivenType(GivenType givenTypeA, GivenType givenTypeB)
  {
    Type2 result = null;

    if (givenTypeA.equals(givenTypeB)) {
      result = givenTypeA;
    }

    return result;
  }

  protected Type2 unifyPowerType(PowerType powerTypeA, PowerType powerTypeB)
  {
    PowerType result = null;

    //try to unify the inner types
    Type2 unified = unify(powerTypeA.getType(), powerTypeB.getType());
    if (unified != null) {
      powerTypeA.setType(unified);
      powerTypeB.setType(unified);
      result = powerTypeA;
      addPossibleDependent(result, unified);
    }

    return result;
  }

  protected Type2 unifyProdType(ProdType prodTypeA, ProdType prodTypeB)
  {
    Type2 result = null;

    List typesA = prodTypeA.getType();
    List typesB = prodTypeB.getType();

    //if the size is not equal, fail
    if (typesA.size() == typesB.size()) {

      //try to unify each type in this product type
      List types = list();
      for (int i = 0; i < typesA.size(); i++) {
        Type2 pTypeA = (Type2) typesA.get(i);
        Type2 pTypeB = (Type2) typesB.get(i);

        Type2 unified = unify(pTypeA, pTypeB);
        if (unified != null) {
          prodTypeA.getType().set(i, unified);
          prodTypeB.getType().set(i, unified);
          addPossibleDependent(prodTypeA, unified);
          addPossibleDependent(prodTypeB, unified);
        }
      }

      result = prodTypeA;
    }

    return result;
  }

  protected Type2 unifySchemaType(SchemaType schemaTypeA,
                                  SchemaType schemaTypeB)
  {
    Type2 result = null;

    //try to unify the two signatures
    Signature sigA = schemaTypeA.getSignature();
    Signature sigB = schemaTypeB.getSignature();
    Signature unified = unifySignature(sigA, sigB);
    if (unified != null) {
      schemaTypeA.setSignature(unified);
      schemaTypeB.setSignature(unified);
      result = schemaTypeA;
    }

    return result;
  }

  protected Type2 unifyGenParamType(GenParamType genParamTypeA,
                                    GenParamType genParamTypeB)
  {
    Type2 result = null;

    if (genParamTypeA.equals(genParamTypeB)) {
      result = genParamTypeA;
    }

    return result;
  }

  //unify 2 signatures
  public Signature unifySignature(Signature sigA, Signature sigB)
  {
    Signature result = null;

    //first check for the special case of where the two references
    //point to the same object
    if (sigA == sigB) {
      return sigA;
    }

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

          //we must iterate over all the names in case the names are
          //declared in different orders
          boolean found = false;
          for (Iterator iterB = listB.iterator(); iterB.hasNext(); ) {
            NameTypePair pairB = (NameTypePair) iterB.next();

            if (pairA.getName().equals(pairB.getName())) {
              Type2 unified =
                unify(unwrapType(pairA.getType()),
                         unwrapType(pairB.getType()));

              if (unified != null) {
                pairA.setType(unified);
                pairB.setType(unified);
                found = true;
                break;
              }
              else {
                return null;
              }
            }
          }

          if (!found) {
            return null;
          }
        }
        result = sigA;
      }
    }

    return result;
  }

  protected Signature unifyVariableSignature(VariableSignature vSig,
                                             Signature sigB)
  {
    Signature result = null;

    Signature possibleSig = getSignature(vSig.getName());
    if (possibleSig != null) {
      result = unifySignature(possibleSig, sigB);
    }
    else {
      //if type2 is also a variable, merge the dependent list
      if (isVariableSignature(sigB)) {
        variableSignature(sigB).getDependent().addAll(vSig.getDependent());
      }

      //let the dependents know of the change
      List dependents = vSig.getDependent();
      for (Iterator iter = dependents.iterator(); iter.hasNext(); ) {
        SchemaType schemaType = (SchemaType) iter.next();
        updateSignature(schemaType, sigB);
      }

      addVarSigName(vSig.getName(), sigB);
      result = sigB;
    }

    return result;
  }
  */

  protected boolean unifyVariableType(VariableType variableType, Type2 type2)
  {
    boolean result = false;

    /*
    if (type2 instanceof VariableType) {
      VariableType vType2 = (VariableType) type2;
      if (vType2.getValue() == variableType) {
        return true;
      }
    }
    else if (variableType.getValue() == variableType) {
      variableType.setValue(type2);
      result = true;
    }
    else {
      result = unify(variableType.getValue(), type2);
    }
    */

    //try to find the type in the unification environment
    Type2 possibleType = getType(variableType.getName());
    if (!isUnknownType(possibleType)) {
      if (possibleType.equals(variableType)) {
        variableType.setValue(type2);
        result = true;
      }
      else {
        result = unify(possibleType, type2);
      }
    }
    else if (!isUnknownType(type2)) {
      variableType.setValue(type2);
      addVarName(variableType.getName(), type2);
      result = true;
    }

    return result;
  }

  protected boolean unifyGivenType(GivenType givenTypeA, GivenType givenTypeB)
  {
    boolean result = givenTypeA.equals(givenTypeB);
    return result;
  }

  protected boolean unifyPowerType(PowerType powerTypeA, PowerType powerTypeB)
  {
    //try to unify the inner types
    boolean result = unify(powerTypeA.getType(), powerTypeB.getType());
    return result;
  }

  protected boolean unifyProdType(ProdType prodTypeA, ProdType prodTypeB)
  {
    boolean result = false;

    List typesA = prodTypeA.getType();
    List typesB = prodTypeB.getType();

    //if the size is not equal, fail
    if (typesA.size() == typesB.size()) {
      Iterator iterA = typesA.iterator();
      Iterator iterB = typesB.iterator();

      //try to unify each type in this product type
      List types = list();
      boolean failed = false;
      while (iterA.hasNext()) {
        Type2 pTypeA = (Type2) iterA.next();
        Type2 pTypeB = (Type2) iterB.next();
        boolean unified = unify(pTypeA, pTypeB);
        if (!unified) {
          failed = true;
        }
      }

      if (!failed) {
        result = true;
      }
    }

    return result;
  }

  protected boolean unifySchemaType(SchemaType schemaTypeA,
                                    SchemaType schemaTypeB)
  {
    //try to unify the two signatures
    Signature sigA = schemaTypeA.getSignature();
    Signature sigB = schemaTypeB.getSignature();
    boolean result = unifySignature(sigA, sigB);
    return result;
  }

  protected boolean unifyGenParamType(GenParamType genParamTypeA,
                                    GenParamType genParamTypeB)
  {
    boolean result = genParamTypeA.equals(genParamTypeB);
    return result;
  }

  //unify 2 signatures
  public boolean unifySignature(Signature sigA, Signature sigB)
  {
    boolean result = false;

    //first check for the special case of where the two references
    //point to the same object
    if (sigA == sigB) {
      return true;
    }

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

          //we must iterate over all the names in case the names are
          //declared in different orders
          boolean found = false;
          for (Iterator iterB = listB.iterator(); iterB.hasNext(); ) {
            NameTypePair pairB = (NameTypePair) iterB.next();

            if (pairA.getName().equals(pairB.getName())) {
              boolean unified = unify(unwrapType(pairA.getType()),
                                      unwrapType(pairB.getType()));

              if (unified) {
                found = true;
                break;
              }
              else {
                return false;
              }
            }
          }

          if (!found) {
            return false;
          }
        }
        result = true;
      }
    }

    return result;
  }

  protected boolean unifyVariableSignature(VariableSignature vSig,
                                           Signature sigB)
  {
    boolean result = false;

    /*
    if (vSig.getValue() == vSig) {
      vSig.setValue(sigB);
      result = true;
    }
    else {
      result = unifySignature(vSig.getValue(), sigB);
    }
    */

    Signature possibleSig = getSignature(vSig.getName());
    if (possibleSig != null) {
      result = unifySignature(possibleSig, sigB);
    }
    else {
      vSig.setValue(sigB);
      addVarSigName(vSig.getName(), sigB);
      result = true;
    }

    return result;
  }

  /**
   * Returns true if and only if the name unifies with the existing
   * type in this environment (if one exists).
   */
  protected boolean unifies(Name name, Type2 type2)
  {
    boolean result = true;
    Type2 storedType = getType(name);

    if (!isUnknownType(storedType)) {
      result = unify(storedType, type2);
    }

    return result;
  }

  protected boolean unifies(Name name, Signature signature)
  {
    boolean result = true;
    Signature storedSig = getSignature(name);

    if (storedSig != null) {
      result = unifySignature(storedSig, signature);
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

  /**
   * This class is similar to a NameTypePair, but is only used to
   * record a list of names that unify to signatures.
   */
  private class NameSignaturePair
  {
    protected DeclName name_;
    protected Signature signature_;

    public NameSignaturePair(DeclName name, Signature signature)
    {
      name_ = name;
      signature_ = signature;
    }

    public void setName(DeclName name)
    {
      name_ = name;
    }

    public DeclName getName()
    {
      return name_;
    }

    public void setSignature(Signature signature)
    {
      signature_ = signature;
    }

    public Signature getSignature()
    {
      return signature_;
    }
  }
}
