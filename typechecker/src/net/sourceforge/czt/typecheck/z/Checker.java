package net.sourceforge.czt.typecheck.z;

import java.io.StringWriter;
import java.util.List;
import java.util.ArrayList;
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
  protected CheckerInfo info_;

  public Checker(CheckerInfo info)
  {
    info_ = info;
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

  protected static boolean isSchemaType(Object o)
  {
    return (o instanceof SchemaType);
  }

  protected static boolean isPowerType(Object o)
  {
    return (o instanceof PowerType);
  }

  protected static boolean isGivenType(Object o)
  {
    return (o instanceof GivenType);
  }

  protected static boolean isGenericType(Object o)
  {
    return (o instanceof GenericType);
  }

  protected static boolean isGenParamType(Object o)
  {
    return (o instanceof GenParamType);
  }

  protected static boolean isProdType(Object o)
  {
    return (o instanceof ProdType);
  }

  protected static boolean isUnknownType(Object o)
  {
    return (o instanceof UnknownType);
  }

  protected static boolean isVariableType(Object o)
  {
    return (o instanceof VariableType);
  }

  protected static boolean isVariableSignature(Object o)
  {
    return (o instanceof VariableSignature);
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
  //one, otherwise, return the input type
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
      termA.getAnns().remove(ann);
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
      PrintUtils.printUnicode(term, writer, manager(), sectName());
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
    return new ArrayList();
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
    List result = new ArrayList(list);
    return result;
  }

  protected UResult unify(Type2 type1, Type2 type2)
  {
    return unificationEnv().unify(type1, type2);
  }

  //a Factory for creating Z terms
  protected Factory factory()
  {
    return info_.factory_;
  }

  //the SectTypeEnv for all parent specifications
  protected SectTypeEnv sectTypeEnv()
  {
    return info_.sectTypeEnv_;
  }

  //the TypeEnv for local variable scopes
  protected TypeEnv typeEnv()
  {
    return info_.typeEnv_;
  }

  //the TypeEnv for pending global declarations
  protected TypeEnv pending()
  {
    return info_.pending_;
  }

  //the UnificationEnv for recording unified generic types
  protected UnificationEnv unificationEnv()
  {
    return info_.unificationEnv_;
  }

  //a section manager
  protected SectionInfo manager()
  {
    return info_.manager_;
  }

  //the factory for creating error messages
  protected ErrorFactory errorFactory()
  {
    return info_.errorFactory_;
  }

  //the current section name
  protected String sectName()
  {
    return info_.sectName_.toString();
  }

  //set the current section name
  protected void sectName(String sectName)
  {
    info_.sectName_.replace(0, info_.sectName_.length(), sectName);
  }

  //the list of errors thrown by retrieving type info
  protected List errors()
  {
    return info_.errors_;
  }

  //the logger instance
  protected Logger logger()
  {
    return info_.logger_;
  }

  //the visitors used to typechecker a spec
  protected SpecChecker specChecker()
  {
    return info_.specChecker_;
  }

  protected ParaChecker paraChecker()
  {
    return info_.paraChecker_;
  }

  protected DeclChecker declChecker()
  {
    return info_.declChecker_;
  }

  protected ExprChecker exprChecker()
  {
    return info_.exprChecker_;
  }

  protected PredChecker predChecker()
  {
    return info_.predChecker_;
  }

  protected PostChecker postChecker()
  {
    return info_.postChecker_;
  }

  //print debuging info
  protected boolean debug()
  {
    return info_.debug_;
  }

  protected void debug(String message)
  {
    if (debug()) {
      System.err.println(message);
    }
  }
}
