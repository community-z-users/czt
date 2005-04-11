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
package net.sourceforge.czt.typecheck.z;

import java.io.StringWriter;
import java.util.List;
import java.util.Iterator;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.typecheck.z.util.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * A super class for the *Checker classes in the typechecker.
 */
abstract public class Checker
  implements TermVisitor
{
  protected static final UResult SUCC = UResult.SUCC;
  protected static final UResult PARTIAL = UResult.PARTIAL;
  protected static final UResult FAIL = UResult.FAIL;

  //the information required for the typechecker classes.
  protected TypeChecker typeChecker_;

  public Checker(TypeChecker typeChecker)
  {
    typeChecker_ = typeChecker;
  }

  /**
   * Double check that this visitor is not being asked to visit a
   * non-Decl object.
   */
  public Object visitTerm(Term term)
  {
    /*
    throw new CztException(this.getClass().getName() +
                           " being asked to visit " +
                           term.getClass().getName());
    */
    System.err.println(this.getClass().getName() +
                       " being asked to visit " +
                       term.getClass().getName());
    return factory().createUnknownType();
  }

  /**
   * If this is a generic type, get the type without the
   * parameters. If not a generic type, return the type
   */
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

  protected static boolean instanceOf(Object o, Class aClass)
  {
    return aClass.isInstance(o);
  }

  //non-safe typecast
  protected static SchemaType schemaType(Object o)
  {
    return (SchemaType) o;
  }

  //non-safe typecast
  protected static PowerType powerType(Object o)
  {
    return (PowerType) o;
  }

  //non-safe typecast
  protected static GivenType givenType(Object o)
  {
    return (GivenType) o;
  }

  //non-safe typecast
  protected static GenericType genericType(Object o)
  {
    return (GenericType) o;
  }

  //non-safe typecast
  protected static GenParamType genParamType(Object o)
  {
    return (GenParamType) o;
  }

  //non-safe typecast
  protected static ProdType prodType(Object o)
  {
    return (ProdType) o;
  }

  //non-safe typecast
  protected static UnknownType unknownType(Object o)
  {
    return (UnknownType) o;
  }

  //non-safe typecast
  protected static VariableType variableType(Object o)
  {
    return (VariableType) o;
  }

  //non-safe typecast
  protected static VariableSignature variableSignature(Object o)
  {
    return (VariableSignature) o;
  }

  //if this is a variable type, returned the resolved type if there is
  //one, otherwise, return the input
  protected Type2 resolve(Type2 type)
  {
    Type2 result = type;
    if (type instanceof VariableType) {
      VariableType vType = (VariableType) type;
      if (vType.getValue() != vType) {
        result = vType.getValue();
      }
    }
    return result;
  }

  //if this is a variable signature, return the resolved signature if there is
  //one, otherwise, return the input
  protected Signature resolve(Signature signature)
  {
    Signature result = signature;
    if (signature instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) signature;
      if (vSig.getValue() != vSig) {
        result = vSig.getValue();
      }
    }
    return result;
  }

  //adds an annotation to a TermA
  protected void addAnn(TermA termA, Object ann)
  {
    if (ann != null) {
      termA.getAnns().add(ann);
    }
  }

  //removes a type annotation from a TermA
  protected void removeAnn(TermA termA, Object ann)
  {
    if (ann != null) {
      List anns = termA.getAnns();
      for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
        Object next = iter.next();
        if (next == ann) {
          iter.remove();
        }
      }
    }
  }

  //removes all type annotations of a particular class from a TermA
  protected void removeAnn(TermA termA, Class aClass)
  {
    List anns = termA.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      Object ann = iter.next();
      if (aClass.isInstance(ann)) {
        iter.remove();
      }
    }
  }

  //adds a type annotation created from a type to a TermA
  protected void addTypeAnn(TermA termA, Type type)
  {
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (typeAnn == null) {
      typeAnn = factory().createTypeAnn(type);
      termA.getAnns().add(typeAnn);
    }
    else {
      typeAnn.setType(type);
    }
  }

  //adds a signature annotation create from a signature to a TermA
  protected void addSignatureAnn(TermA termA, Signature signature)
  {
    SignatureAnn signatureAnn =
      (SignatureAnn) termA.getAnn(SignatureAnn.class);

    if (signatureAnn == null) {
      signatureAnn = factory().createSignatureAnn(signature);
      termA.getAnns().add(signatureAnn);
    }
    else {
      signatureAnn.setSignature(signature);
    }
  }

  protected TypeAnn getTypeAnn(TermA termA)
  {
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (typeAnn == null) {
      typeAnn = factory().createTypeAnn();
      addAnn(termA, typeAnn);
    }

    return typeAnn;
  }

  protected Type2 getTypeFromAnns(TermA termA)
  {
    Type result = factory().createUnknownType();
    TypeAnn typeAnn = (TypeAnn) termA.getAnn(TypeAnn.class);

    if (typeAnn != null) {
      result = typeAnn.getType();
    }
    return unwrapType(result);
  }

  //returns true if and only if 'list' contains a reference to 'o'
  protected static boolean containsDoubleEquals(List list, Object o)
  {
    boolean result = false;

    for (Iterator iter = list.iterator(); iter.hasNext(); ) {
      Object next = iter.next();
      if (next == o) {
        result = true;
        break;
      }
    }
    return result;
  }

  //returns true if and only if the specified type contains a variable
  //type
  protected boolean containsVariableType(Type2 type2)
  {
    return UnificationEnv.containsVariable(type2);
  }

  //add an error to the list of error annotation
  protected void error(ErrorAnn errorAnn)
  {
    errors().add(errorAnn);
  }

  //add an error to the list of error messages, and as an annotation
  //to the term
  protected void error(TermA termA, ErrorAnn errorAnn)
  {
    termA.getAnns().add(errorAnn);
    error(errorAnn);
  }

  protected void error(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = errorAnn(termA, error, params);
    error(termA, errorAnn);
  }

  protected ErrorAnn errorAnn(TermA termA, ErrorMessage error, Object [] params)
  {
    ErrorAnn errorAnn = new ErrorAnn(error.toString(), params, sectInfo(),
                                     sectName(), nearestLocAnn(termA));
    return errorAnn;
  }

  protected void removeError(TermA termA)
  {
    List anns = termA.getAnns();
    for (Iterator iter = anns.iterator(); iter.hasNext(); ) {
      Object ann = iter.next();
      if (ann instanceof ErrorAnn) {
        iter.remove();
        errors().remove(ann);
      }
    }
  }

  //converts a Term to a string
  protected String format(Term term)
  {
    try {
      StringWriter writer = new StringWriter();
      PrintUtils.printUnicode(term, writer, sectInfo(), sectName());
      return writer.toString();
    }
    catch (Exception e) {
      String message = "Cannot be printed";
      return message;
    }
  }

  protected String formatType(Type type)
  {
    //TypeFormatter formatter = new TypeFormatter();
    //Expr expr = (Expr) type.accept(formatter);
    //return format(expr);
    return type.toString();
  }

  //get the position of a TermA from its annotations
  protected String position(TermA termA)
  {
    String result = "Unknown location: ";

    LocAnn locAnn = nearestLocAnn(termA);
    if (locAnn != null) {
      result = "\"" + locAnn.getLoc() + "\", ";
      result += "line " + locAnn.getLine() + ": ";
    }
    else {
      result = "No location information";
    }

    return result;
  }

  //find the closest LocAnn
  protected LocAnn nearestLocAnn(TermA termA)
  {
    LocAnn result = (LocAnn) termA.getAnn(LocAnn.class);

    if (result == null) {
      for (int i = 0; i < termA.getChildren().length; i++) {
        Object next = termA.getChildren()[i];
        if (next instanceof TermA) {
          LocAnn nextLocAnn = nearestLocAnn((TermA) next);
          return nextLocAnn;
        }
      }
    }
    return result;
  }

  protected static List list()
  {
    return new java.util.ArrayList();
  }

  protected static List list(Object o)
  {
    List result = list();
    result.add(o);
    return result;
  }

  protected static List list(Object o1, Object o2)
  {
    List result = list(o1);
    result.add(o2);
    return result;
  }

  protected static List list(List list)
  {
    List result = new java.util.ArrayList(list);
    return result;
  }

  protected UResult unify(Type2 type1, Type2 type2)
  {
    return unificationEnv().unify(type1, type2);
  }

  //a Factory for creating Z terms
  protected Factory factory()
  {
    return typeChecker_.factory_;
  }

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv()
  {
    return typeChecker_.sectTypeEnv_;
  }

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv()
  {
    return typeChecker_.typeEnv_;
  }

  //the TypeEnv for pending global declarations
  protected TypeEnv pending()
  {
    return typeChecker_.pending_;
  }

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv()
  {
    return typeChecker_.unificationEnv_;
  }

  //a section manager
  protected SectionInfo sectInfo()
  {
    return typeChecker_.sectInfo_;
  }

  //the current section name
  protected String sectName()
  {
    return typeChecker_.sectName_.toString();
  }

  //set the current section name
  protected void sectName(String sectName)
  {
    typeChecker_.sectName_.replace(0, typeChecker_.sectName_.length(),
                                   sectName);
  }

  //the list of errors thrown by retrieving type info
  protected List errors()
  {
    return typeChecker_.errors_;
  }

  //the logger instance
  protected Logger logger()
  {
    return typeChecker_.logger_;
  }

  //typecheck a file using an instance of this typechecker
  protected List typecheck(TermA termA, SectionInfo sectInfo)
  {
    return TypeCheckUtils.typecheck(termA, sectInfo);
  }

  //the visitors used to typechecker a spec
  protected Checker specChecker()
  {
    return typeChecker_.specChecker_;
  }

  protected Checker paraChecker()
  {
    return typeChecker_.paraChecker_;
  }

  protected Checker declChecker()
  {
    return typeChecker_.declChecker_;
  }

  protected Checker exprChecker()
  {
    return typeChecker_.exprChecker_;
  }

  protected Checker predChecker()
  {
    return typeChecker_.predChecker_;
  }

  protected Checker postChecker()
  {
    return typeChecker_.postChecker_;
  }


  //check for type mismatches in a list of decls. Add an ErrorAnn to
  //any name that is in error
  protected void checkForDuplicates(List<NameTypePair> pairs, TermA termA)
  {
    for (int i = 0; i < pairs.size(); i++) {
      NameTypePair first = pairs.get(i);
      for (int j = i + 1; j < pairs.size(); j++) {
        NameTypePair second = pairs.get(j);
        if (first.getName().equals(second.getName())) {
          Type2 firstType = unwrapType(first.getType());
          Type2 secondType = unwrapType(second.getType());
          UResult unified = unify(firstType, secondType);

          //if the types don't agree, raise an error
          if (unified == FAIL) {
            Object [] params = {first.getName(), firstType, secondType};
            error(termA, ErrorMessage.TYPE_MISMATCH_IN_SIGNATURE, params);
          }
          //if the types do agree, we don't need the second declaration
          else {
            pairs.remove(j--);
          }
        }
      }
    }
  }

  protected Type instantiate(Type type)
  {
    Type result = factory().createUnknownType();

    if (type instanceof GenericType) {
      Type2 optionalType =
        (Type2) factory().cloneTerm(genericType(type).getType());
      if (genericType(type).getOptionalType() != null) {
        optionalType = genericType(type).getOptionalType();
      }
      Type2 instantiated = instantiate(optionalType);
      genericType(type).setOptionalType(instantiated);
      result = type;
    }
    else {
      result = instantiate((Type2) type);
    }

    return result;
  }

  protected Type2 instantiate(Type2 type)
  {
    Type2 result = factory().createUnknownType();

    if (type instanceof GenParamType) {
      GenParamType genParamType = (GenParamType) type;
      DeclName genName = genParamType.getName();

      //try to get the type from the UnificationEnv
      Type unificationEnvType = unificationEnv().getType(genName);

      //if this type's reference is in the parameters
      if (containsDoubleEquals(typeEnv().getParameters(), genName)) {
        result = type;
      }
      else if (unificationEnvType instanceof UnknownType &&
               unknownType(unificationEnvType).getName() == null) {
        VariableType vType = factory().createVariableType();
        result = vType;
        unificationEnv().addGenName(genName, result);
      }
      else if (unificationEnvType instanceof Type2) {
        result = (Type2) unificationEnvType;
      }
      else {
        throw new CztException("Cannot instantiate " + type);
      }
    }
    else if (type instanceof VariableType) {
      VariableType vType = (VariableType) type;
      Type2 possibleType = vType.getValue();
      if (possibleType instanceof UnknownType &&
          unknownType(possibleType).getName() == null) {
        result = vType;
      }
      else if (possibleType instanceof Type2) {
        result = (Type2) possibleType;
      }
      else {
        throw new CztException("Cannot instantiate " + type);
      }
    }
    else if (type instanceof PowerType) {
      PowerType powerType = (PowerType) type;
      Type2 replaced = instantiate(powerType.getType());
      powerType.setType(replaced);
      result = powerType;
    }
    else if (type instanceof GivenType) {
      result = type;
    }
    else if (type instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) type;
      Signature signature = schemaType.getSignature();
      instantiate(signature);
      result = schemaType;
    }
    else if (type instanceof ProdType) {
      ProdType prodType = (ProdType) type;
      //the list of types for the new instantiated product
      for (int i = 0; i < prodType.getType().size(); i++) {
        Type2 next = (Type2) prodType.getType().get(i);

        Type2 replaced = instantiate(next);
        prodType.getType().set(i, replaced);
      }

      result = prodType;
    }
    return result;
  }

  protected void instantiate(Signature signature)
  {
    List<NameTypePair> pairs = signature.getNameTypePair();
    for (NameTypePair pair : pairs) {
      Type replaced = instantiate(pair.getType());
      pair.setType(replaced);
    }
  }

  protected boolean isPending(GenericType gType)
  {
    List<DeclName> params = typeEnv().getParameters();
    DeclName param = (DeclName) gType.getName().get(0);
    return containsDoubleEquals(params, param);
  }

  //if there are generics in the current type env, return a new
  //GenericType with this Type2 as the type
  protected Type addGenerics(Type2 type)
  {
    Type result = null;
    List<DeclName> params = typeEnv().getParameters();
    if (params.size() > 0) {
      result = factory().createGenericType(params, type, null);
    }
    else {
      result = type;
    }

    return result;
  }

  //add generic types from a list of DeclNames to the TypeEnv
  protected void addGenParamTypes(List<DeclName> declNames)
  {
    typeEnv().setParameters(declNames);

    //add each DeclName and its type
    List<String> names = list();
    for (DeclName declName : declNames) {
      //declName.setId("" + id++);

      //check if there are strokes in the name
      if (declName.getStroke().size() > 0) {
        Object [] params = {declName};
        error(declName, ErrorMessage.STROKE_IN_GEN, params);
      }

      GenParamType genParamType = factory().createGenParamType(declName);
      PowerType powerType = factory().createPowerType(genParamType);

      //check if a generic parameter type is redeclared
      if (names.contains(declName.getWord())) {
        Object [] params = {declName};
        error(declName, ErrorMessage.REDECLARED_GEN, params);
      }
      else {
        names.add(declName.getWord());
      }

      //add the name and type to the TypeEnv
      typeEnv().add(declName, powerType);
    }
  }

  //gets the type of the expression represented by a name
  protected Type getType(RefName name)
  {
    //get the type from the TypeEnv
    Type type = typeEnv().getType(name);

    //if the type environment did not know of this expression.
    //then ask the pending env
    if (type instanceof UnknownType) {
      type = pending().getType(name);
    }

    //if the pending environment did not know of this expression,
    //then ask the SectTypeEnv
    if (type instanceof UnknownType) {
      Type sectTypeEnvType = sectTypeEnv().getType(name);
      if (!instanceOf(sectTypeEnvType, UnknownType.class)) {
        type = (Type) factory().cloneTerm(sectTypeEnvType);
      }
    }

    //if not in either environments, return a variable type with the
    //specified name
    if (type instanceof UnknownType) {
      DeclName declName =
        factory().createDeclName(name.getWord(), name.getStroke(), null);
      VariableType vType = factory().createVariableType();
      vType.setName(declName);
      type = vType;

      //add an UndeclaredAnn
      UndeclaredAnn ann = new UndeclaredAnn();
      name.getAnns().add(ann);
    }
    else {
      //remove an UndeclaredAnn if there is one
      removeAnn(name, UndeclaredAnn.class);
    }

    return type;
  }

  //get a name/type pair corresponding with a particular name
  //return null if this name is not in the signature
  protected NameTypePair findInSignature(DeclName declName,
                                         Signature signature)
  {
    NameTypePair result = null;
    List<NameTypePair> pairs = signature.getNameTypePair();
    for (NameTypePair pair : pairs) {
      if (pair.getName().equals(declName)) {
        result = pair;
        break;
      }
    }
    return result;
  }

  protected NameTypePair findInSignature(RefName refName,
                                         Signature signature)
  {
    DeclName declName = factory().createDeclName(refName);
    return findInSignature(declName, signature);
  }

  //print debuging info
  protected boolean debug()
  {
    return typeChecker_.debug_;
  }

  protected void setDebug(boolean b)
  {
    typeChecker_.debug_ = b;
  }

  protected void debug(String message)
  {
    if (debug()) {
      System.err.println(message);
    }
  }
}
