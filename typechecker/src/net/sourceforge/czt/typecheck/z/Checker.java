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
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * A super class for the *Checker classes in the typechecker.
 */
abstract class Checker
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
    throw new CztException(this.getClass().getName() +
                           " being asked to visit " +
                           term.getClass().getName());
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
    return UnificationEnv.containsVariableType(type2);
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

  //clone is used to do a recursive clone on a type
  protected Type cloneType(Type type)
  {
    CloningVisitor cloningVisitor = new CloningVisitor(factory());
    return (Type) type.accept(cloningVisitor);
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

  //the factory for creating error messages
  protected ErrorFactory errorFactory()
  {
    return typeChecker_.errorFactory_;
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

  //the visitors used to typechecker a spec
  protected SpecChecker specChecker()
  {
    return typeChecker_.specChecker_;
  }

  protected ParaChecker paraChecker()
  {
    return typeChecker_.paraChecker_;
  }

  protected DeclChecker declChecker()
  {
    return typeChecker_.declChecker_;
  }

  protected ExprChecker exprChecker()
  {
    return typeChecker_.exprChecker_;
  }

  protected PredChecker predChecker()
  {
    return typeChecker_.predChecker_;
  }

  protected PostChecker postChecker()
  {
    return typeChecker_.postChecker_;
  }

  //print debuging info
  protected boolean debug()
  {
    return typeChecker_.debug_;
  }

  protected void debug(String message)
  {
    if (debug()) {
      System.err.println(message);
    }
  }
}
