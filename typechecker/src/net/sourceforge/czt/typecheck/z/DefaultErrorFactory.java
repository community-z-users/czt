package net.sourceforge.czt.typecheck.z;

import java.util.Iterator;
import java.io.StringWriter;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.SectionManager;

import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * The default error message factory.
 */
public class DefaultErrorFactory
  implements ErrorFactory
{
  /** A section manager. */
  protected SectionManager manager_;

  public DefaultErrorFactory(SectionManager manager)
  {
    manager_ = manager;
  }

  public ErrorAnn unknownType(Expr expr)
  {
    String position = position(expr);
    String message = "Type of " + format(expr) + " cannot be inferred";
    return errorAnn(position, message);
  }

  public ErrorAnn undeclaredIdentifier(RefExpr refExpr)
  {
    String position = position(refExpr);
    String message = "Undeclared identifier: " + format(refExpr.getRefName());
    return errorAnn(position, message);
  }

  public ErrorAnn parametersNotDetermined(Expr expr)
  {
    String position = position(expr);
    String message = "Implicit parameters not determined\n" +
      "\tExpression: " + format(expr);
    return errorAnn(position, message);
  }

  public ErrorAnn redeclaredSection(ZSect zSect)
  {
    String position = position(zSect);
    String message =
      "Section with name " + zSect.getName() +
      " has previously been declared";
    return errorAnn(position, message);
  }

  public ErrorAnn redeclaredParent(Parent parent, String sectionName)
  {
    String position = position(parent);
    String message =
      "Parent " + parent.getWord() + " is multiply " +
      " included for section " + sectionName;
    return errorAnn(position, message);
  }

  public ErrorAnn selfParent(Parent parent)
  {
    String position = position(parent);
    String message =
      "Section " + parent.getWord() + " has itself as a parent";
    return errorAnn(position, message);
  }

  public ErrorAnn strokeInGiven(DeclName declName)
  {
    String position = position(declName);
    String message =
      "Given type name " + format(declName) + " contains stroke";
    return errorAnn(position, message);
  }

  public ErrorAnn strokeInGen(DeclName declName)
  {
    String position = position(declName);
    String message =
      "Generic type name " + format(declName) + " contains stroke";
    return errorAnn(position, message);
  }

  public ErrorAnn redeclaredGiven(DeclName declName)
  {
    String position = position(declName);
    String message =
      "Given type name " + format(declName) + " multiply declared";
    return errorAnn(position, message);
  }

  public ErrorAnn redeclaredGen(DeclName declName)
  {
    String position = position(declName);
    String message =
      "Generic type name " + format(declName) +
      " multiply declared in generic paragraph definition";
    return errorAnn(position, message);
  }

  public ErrorAnn nonSetInFreeType(Expr expr, Type type)
  {
    String position = position(expr);
    String message =
      "Set expression required for free type\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSetInDecl(Expr expr, Type type)
  {
    String position = position(expr);
    String message =
      "Set expression required in declaration\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSetInPowerExpr(Expr expr, Type type)
  {
    String position = position(expr);
    String message =
      "Set expression required in power expr\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSetInProdExpr(Expr expr, Type type, int exprPos)
  {
    String position = position(expr);
    String message =
      "Argument " + exprPos + " must be a set expression\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tArgument " + position + " type: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSetInInstantiation(Expr expr, Type type)
  {
    String position = position(expr);
    String message =
      "Set expression required in generic instantiation\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInInclDecl(InclDecl inclDecl, Type type)
  {
    String position = position(inclDecl);
    String message =
      "Included declaration " + format(inclDecl) + " is not a schema\n" +
      "\tFound type: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonProdTypeInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                            Type type)
  {
    String position = position(tupleSelExpr);
    String message =
      "Argument of tuple selection must be a tuple\n" +
      "\tExpression: " + format(tupleSelExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInThetaExpr(ThetaExpr thetaExpr, Type type)
  {
    String position = position(thetaExpr);
    String message =
      "Schema expression required as argument to theta expression\n" +
      "\tExpression: " + format(thetaExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInDecorExpr(DecorExpr decorExpr, Type type)
  {
    String position = position(decorExpr);
    String message =
      "Schema expression in decorated expression\n" +
      "\tExpression: " + format(decorExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInQnt1Expr(Qnt1Expr qnt1Expr, Type type)
  {
    String position = position(qnt1Expr);
    String message =
      "Schema expression required as predicate to quantified expression" +
      "\n\tExpression: " + format(qnt1Expr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInHideExpr(HideExpr hideExpr, Type type)
  {
    String position = position(hideExpr);
    String message =
      "Attemping to hide variables from non-schema expression\n" +
      "\tExpression: " + format(hideExpr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInPreExpr(PreExpr preExpr, Type type)
  {
    String position = position(preExpr);
    String message =
      "Schema expression required in precondition expression\n" +
      "\tExpression: " + format(preExpr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInRenameExpr(RenameExpr renameExpr, Type type)
  {
    String position = position(renameExpr);
    String message =
      "Schema expression required in rename expression\n" +
      "\tExpression: " + format(renameExpr) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInSchExpr2(SchExpr2 schExpr2, Type type)
  {
    String stExpr = schExpr2Type(schExpr2);
    String position = position(schExpr2);
    String message =
      "Non-schema expression in " + stExpr + " \n" +
      "\tExpression: " + format(schExpr2) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInBindSelExpr(BindSelExpr bindSelExpr, Type type)
  {
    String position = position(bindSelExpr);
    String message =
      "Argument of binding selection must have schema type\n" +
      "\tExpression: " + format(bindSelExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn incompatibleSignatures(SchExpr2 schExpr2,
                                         Name name,
                                         Type lType,
                                         Type rType)
  {
    String stExpr = schExpr2Type(schExpr2);
    String position = position(schExpr2);
    String message =
      "Incompatible signatures in " + stExpr +
      " for name " + format(name) + "\n" +
      "\tExpression: " + format(schExpr2) + "\n" +
      "\tFirst Type: " + formatType(lType) + "\n" +
      "\tSecond Type: " + formatType(rType);
    return errorAnn(position, message);
  }

  public ErrorAnn nonExistentSelection(BindSelExpr bindSelExpr)
  {
    String position = position(bindSelExpr);
    String message =
       "Non-existent component selected in binding selection\n" +
      "\tExpression: " + format(bindSelExpr);
    return errorAnn(position, message);
  }

  public ErrorAnn nonExistentNameInHideExpr(HideExpr hideExpr, Name name)
  {
    String position = position(hideExpr);
    String message =
       "Non-existent component hidden\n" +
      "\tExpression: " + format(hideExpr) + "\n" +
      "\tComponent: " + format(name);
    return errorAnn(position, message);
  }

  public ErrorAnn nonFunctionInApplExpr(ApplExpr applExpr, Type type)
  {
    String position = position(applExpr);
    String message =
      "Application of a non-function\n" +
      "\tExpression: " + format(applExpr) + "\n" +
      "\tFound type: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn indexErrorInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                           ProdType prodType)
  {
    String position = position(tupleSelExpr);
    String message =
      "Tuple selection index out of bounds\n" +
      "\tExpression: " + format(tupleSelExpr) + "\n" +
      "\tArgument length: " + prodType.getType().size();
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInSetExpr(Expr expr,
                                        Type type,
                                        Type expectedType)
  {
    String position = position(expr);
    String message =
      "Type mismatch is set expression\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type) + "\n" +
      "\tExpected type: " + formatType(expectedType);
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInCondExpr(CondExpr condExpr,
                                         Type leftType,
                                         Type rightType)
  {
    String position = position(condExpr);
    String message =
      "Type mismatch in conditional expression\n" +
      "\tExpression: " + format(condExpr) + "\n" +
      "\tThen type: " + formatType(leftType) + "\n" +
      "\tElse type: " + formatType(rightType);
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInApplExpr(ApplExpr applExpr,
                                         Type expected,
                                         Type actual)
  {
    String position = position(applExpr);
    String message =
      "Argument to function application has unexpected type\n" +
      "\tExpression: " + format(applExpr) + "\n" +
      "\tExpected type: " + formatType(expected) + "\n" +
      "\tActual type: " + formatType(actual);
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInMemPred(MemPred memPred,
                                        Type leftType,
                                        Type rightType)
  {
    String position = position(memPred);
    String message =
      "Type mismatch in membership predicate\n" +
      "\tPredicate: " + format(memPred) + "\n" +
      "\tLHS type: " + formatType(leftType) + "\n" +
      "\tRHS type: " + formatType(rightType);
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInEquality(MemPred memPred,
                                         Type leftType,
                                         Type rightType)
  {
    String position = position(memPred);
    String message =
      "Type mismatch in equality\n" +
      "\tPredicate: " + format(memPred) + "\n" +
      "\tLHS type: " + formatType(leftType) + "\n" +
      "\tRHS type: " + formatType(rightType);
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInChainRelation(AndPred andPred,
                                              Type firstUnification,
                                              Type secondUnification)
  {
    String position = position(andPred);
    String message =
      "Type mismatch in chain relation\n" +
      "Middle expression unifies to different types\n" +
      "\tChain relation: " + format(andPred) + "\n " +
      "\tFirst type: " + formatType(firstUnification) + "\n" +
      "\tSecond type: " + formatType(secondUnification);
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInRelOp(MemPred memPred,
                                      Type leftType,
                                      Type rightType)
  {
    String position = position(memPred);
    String message =
      "Type mismatch in relation\n" +
      "\tPredicate: " + format(memPred) + "\n" +
      "\tType: " + formatType(leftType) + "\n" +
      "\tExpected: " + formatType(rightType);
    return errorAnn(position, message);
  }

  public ErrorAnn duplicateInBindExpr(BindExpr bindExpr, DeclName declName)
  {
    String position = position(bindExpr);
    String message = "Duplicate name in binding expr: " + format(declName);
    return errorAnn(position, message);
  }

  protected String schExpr2Type(SchExpr2 schExpr2)
  {
    String result = new String("schema expr");
    if (schExpr2 instanceof AndExpr) {
      result = new String("schema conjunction");
    }
    else if (schExpr2 instanceof OrExpr) {
      result = new String("schema disjunction");
    }
    else if (schExpr2 instanceof ImpliesExpr) {
      result = new String("schema implication");
    }
    else if (schExpr2 instanceof IffExpr) {
      result = new String("schema equivalence");
    }
    else if (schExpr2 instanceof ProjExpr) {
      result = new String("schema projection");
    }
    else if (schExpr2 instanceof PipeExpr) {
      result = new String("schema piping");
    }
    else if (schExpr2 instanceof CompExpr) {
      result = new String("schema composition");
    }

    return result;
  }

  protected ErrorAnn errorAnn(String position, String message)
  {
    return new ErrorAnn(position, message);
  }

  //converts a Term to a string
  protected String format(Term term)
  {
    try {
      StringWriter writer = new StringWriter();
      PrintUtils.printUnicode(term, writer, manager_);
      return writer.toString();
    }
    catch (Exception e) {
      return "Cannot be printed";
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
    String result = "Unknown location\n";

    for (Iterator iter = termA.getAnns().iterator(); iter.hasNext(); ) {
      Object next = iter.next();

      if (next instanceof LocAnn) {
        LocAnn locAnn = (LocAnn) next;
        result = "File: " + locAnn.getLoc() + "\n";
        result += "Position: " + locAnn.getLine() +
          ", " + locAnn.getCol() + "\n";
        break;
      }
    }

    return result;
  }
}
