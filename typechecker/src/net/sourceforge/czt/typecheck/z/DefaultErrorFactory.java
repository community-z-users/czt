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

import java.util.List;
import java.io.StringWriter;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.SectionInfo;

import net.sourceforge.czt.typecheck.util.typingenv.*;

/**
 * The default error message factory.
 */
public class DefaultErrorFactory
  implements ErrorFactory
{
  /** A section information manager. */
  protected SectionInfo sectInfo_;

  /** The current section. */
  protected String sectName_;

  public DefaultErrorFactory(SectionInfo sectInfo)
  {
    sectInfo_ = sectInfo;
  }

  public void setSection(String sectName)
  {
    sectName_ = sectName;
  }

  public String getSection()
  {
    return sectName_;
  }

  public ErrorAnn unknownType(Expr expr)
  {
    String position = position(expr);
    String message = "Type of " + format(expr) + " cannot be inferred";
    return errorAnn(position, message);
  }

  public ErrorAnn undeclaredIdentifier(RefName refName)
  {
    String position = position(refName);
    String message = "Undeclared identifier: " + format(refName);
    return errorAnn(position, message);
  }

  public ErrorAnn parametersNotDetermined(Expr expr)
  {
    String position = position(expr);
    String message = "Implicit parameters not determined\n" +
      "\tExpression: " + format(expr);
    return errorAnn(position, message);
  }

  public ErrorAnn parameterMismatch(RefExpr refExpr, int paramLength)
  {
    String position = position(refExpr);
    String message = "Name " + format(refExpr.getRefName()) + " expects " +
      paramLength + " parameters";
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

  public ErrorAnn redeclaredGen(DeclName declName)
  {
    String position = position(declName);
    String message =
      "Generic type name " + format(declName) +
      " multiply declared in generic paragraph definition";
    return errorAnn(position, message);
  }

  public ErrorAnn redeclaredGlobalName(DeclName declName)
  {
    //throw new RuntimeException("Redeclared " + declName);
    String position = position(declName);
    String message =
      "Global name " + format(declName) + " multiply declared";
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

  public ErrorAnn nonSetInProdExpr(ProdExpr prodExpr, Type type, int exprPos)
  {
    String position = position(prodExpr);
    String message =
      "Argument " + exprPos + " of cross produce must be a set expression\n" +
      "\tExpression: " + format(prodExpr) + "\n" +
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

  public ErrorAnn nonSchExprInExprPred(ExprPred exprPred, Type type)
  {
    String position = position(exprPred);
    String message =
      "Schema expression required in expression predicate\n" +
      "\tExpression: " + format(exprPred) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn duplicateNameInRenameExpr(RenameExpr renameExpr,
                                            RefName refName)
  {
    String position = position(renameExpr);
    String message =
      "Duplicate name in rename expression\n" +
      "\tExpression: " + format(renameExpr) + "\n" +
      "\tName: " + format(refName);
    return errorAnn(position, message);
  }

  public ErrorAnn typeMismatchInRenameExpr(RenameExpr renameExpr,
                                    Name name,
                                    Type typeA, Type typeB)
  {
    String position = position(renameExpr);
    String message =
      "Type mismatch for merged declaration in rename expression\n" +
      "\tExpression: " + format(renameExpr) + "\n" +
      "\tName: " + format(name) + "\n" +
      "\tFirst type: " + formatType(typeA) + "\n" +
      "\tSecond type: " + formatType(typeB);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInSchExpr2(SchExpr2 schExpr2, Type type)
  {
    String sExpr = schExprType(schExpr2);
    String position = position(schExpr2);
    String message =
      "Non-schema expression in " + sExpr + " \n" +
      "\tExpression: " + format(schExpr2) + "\n" +
      "\tType: " + formatType(type);
    return errorAnn(position, message);
  }

  public ErrorAnn nonSchExprInQnt1Expr(Qnt1Expr qnt1Expr, Type type)
  {
    String sExpr = qnt1ExprType(qnt1Expr);
    String position = position(qnt1Expr);
    String message =
      "Schema expression required as predicate to " + sExpr + " \n" +
      "\tExpression: " + format(qnt1Expr) + "\n" +
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

  public ErrorAnn typeMismatchInSignature(TermA termA,
                                          DeclName declName,
                                          Type lType,
                                          Type rType)
  {

    String position = position(termA);
    String message =
      "Type mismatch in declaration of " + format(declName) + "\n";
    if (termA instanceof Expr || termA instanceof ExprPred) {
      message += "\tExpression: " + format(termA) + "\n";
    }
    message +=  "\tFirst Type: " + formatType(lType) + "\n" +
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

  public ErrorAnn typeMismatchInSetExpr(SetExpr setExpr,
                                        Type type,
                                        Type expectedType)
  {
    String position = position(setExpr);
    String message =
      "Type mismatch in set expression\n" +
      "\tExpression: " + format(setExpr) + "\n" +
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

  protected String schExprType(SchExpr2 schExpr2)
  {
    String result = new String("schema expression");
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

  protected String qnt1ExprType(Qnt1Expr qnt1Expr)
  {
    String result = new String("schema quantification expression");
    if (qnt1Expr instanceof ForallExpr) {
      result = new String("schema universal quantification expression");
    }
    else if (qnt1Expr instanceof ExistsExpr) {
      result = new String("schema existential quantification expression");
    }
    else if (qnt1Expr instanceof Exists1Expr) {
      result =
        new String("schema unique existential quantification expression");
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
      PrintUtils.printUnicode(term, writer, sectInfo_, sectName_);
      return writer.toString();
    }
    catch (Exception e) {
      String message = "Cannot be printed\n";
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
        else if (next instanceof List) {
          List list = (List) next;
          for (int j = 0; j < list.size(); j++) {
            Object lNext = list.get(j);
            if (lNext instanceof TermA) {
              LocAnn nextLocAnn = nearestLocAnn((TermA) lNext);
              return nextLocAnn;
            }
          }
        }
      }
    }
    return result;
  }
}
