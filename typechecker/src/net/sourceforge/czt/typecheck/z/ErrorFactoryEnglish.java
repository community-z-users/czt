package net.sourceforge.czt.typecheck.z;

import java.util.Iterator;
import java.io.StringWriter;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.SectionManager;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.TypeException;

public class ErrorFactoryEnglish
  implements ErrorFactory
{
  private SectionManager manager_;

  public ErrorFactoryEnglish(SectionManager manager)
  {
    manager_ = manager;
  }

  public String unknownType(Expr expr)
  {
    String message = "At " + position(expr) + "\n";
    message += "Type of " + format(expr) + " cannot be inferred";
    return message;
  }

  public String redeclaredSection(String sectionName)
  {
    String message = "Section with name " + sectionName +
      " has previously been declared";
    return message;
  }

  public String redeclaredParent(Parent parent, String sectionName)
  {
    String message = "Parent " + parent.getWord() + " is multiply " +
      " included for section " + sectionName;
    return message;
  }

  public String selfParent(String sectionName)
  {
    String message = "Section " + sectionName +
      " has itself as a parent";
    return message;
  }

  public String strokeInGiven(DeclName declName)
  {
    String message = "Given type name " + format(declName) + 
      " contains stroke";
    return message;
  }

  public String strokeInGen(DeclName declName)
  {
    String message = "Generic type name " + format(declName) + 
      " contains stroke";
    return message;
  }

  public String redeclaredGiven(DeclName declName)
  {
    String message = "Given type name " + format(declName) +
      " multiply declared";
    return message;
  }

  public String redeclaredGen(DeclName declName)
  {
    String message = "Generic type name " + format(declName) +
      " multiply declared in generic paragraph definition";
    return message;
  }

  public String nonSetInFreeType(Expr expr, Type type)
  {
    String message = "Set expression required for free type\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type);
    return message;
  }

  public String nonSetInDecl(Expr expr, Type type)
  {
    String message = "Set expression required in declaration\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type);
    return message;
  }

  public String nonSetInPowerExpr(Expr expr, Type type)
  {
    String message = "Set expression required in power expr\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type);
    return message;
  }

  public String nonSetInProdExpr(Expr expr, Type type, int position)
  {
    String message = "Argument " + position + " must be a set expression\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tArgument " + position + " type: " + formatType(type);
    return message;
  }

  public String nonSchExprInInclDecl(InclDecl inclDecl)
  {
    String message = "Included declaration " + format(inclDecl) +
      " is not a schema";
    return message;
  }

  public String nonProdTypeInTupleSelExpr(TupleSelExpr tupleSelExpr,
					  Type type)
  {
    String message = "Argument of tuple selection must be a tuple\n" +
      "\tExpression: " + format(tupleSelExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return message;
  }

  public String nonSchExprInThetaExpr(ThetaExpr thetaExpr, Type type)
  {
    String message =
      "Schema expression required as argument to a theta expr\n" +
      "\tExpression: " + format(thetaExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return message;
  }

  public String nonSchTypeInBindSelExpr(BindSelExpr bindSelExpr, Type type)
  {
    String message = "Argument of binding selection must have schema type\n" +
      "\tExpression: " + format(bindSelExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return message;
  }

  public String nonExistentSelection(BindSelExpr bindSelExpr, Type type)
  {
    String message =
      "Non-existent component selected in binding selection\n" +
      "\tExpression: " + format(bindSelExpr) + "\n" +
      "\tArgument type: " + formatType(type);
    return message;
  }

  public String nonFunctionInApplExpr(ApplExpr applExpr, Type type)
  {
    String message = "Application of a non-function\n" +
      "\tExpression: " + format(applExpr) + "\n" +
      "\tFound type: " + formatType(type);
    return message;
  }

  public String indexErrorInTupleSelExpr(TupleSelExpr tupleSelExpr, 
					 ProdType prodType)
  {
    String message = "Tuple selection index out of bounds\n" +
      "\tExpression: " + format(tupleSelExpr) + "\n" +
      "\tArgument length: " + prodType.getType().size();
    return message;
  }

  public String typeMismatchInSetExpr(Expr expr, Type type, Type expectedType)
  {
    String message = "Type mismatch is set expression\n" +
      "\tExpression: " + format(expr) + "\n" +
      "\tType: " + formatType(type) + "\n" +
      "\tExpected type: " + formatType(expectedType);
    return message;
  }

  public String typeMismatchInCondExpr(CondExpr condExpr,
				       Type leftType,
				       Type rightType)
  {
    String message = "Type mismatch in conditional expression\n" +
      "\tExpression: " + format(condExpr) + "\n" +
      "\tThen type: " + formatType(leftType) + "\n" +
      "\tElse type: " + formatType(rightType);
    return message;
  }

  public String typeMismatchInApplExpr(ApplExpr applExpr, 
				       Type expected,
				       Type actual)
  {
    String message = "Argument to function application has unexpected type\n" +
      "\tExpression: " + format(applExpr) + "\n" +
      "\tExpected type: " + formatType(expected) + "\n" +
      "\tActual type: " + formatType(actual);
    return message;
  }

  public String typeMismatchInMemPred(MemPred memPred,
				      Type leftType,
				      Type rightType)
  {
    String message = "Type mismatch in membership predicate\n" +
      "\tPredicate: " + format(memPred) + "\n" +
      "\tLHS type: " + formatType(leftType) + "\n" +
      "\tRHS type: " + formatType(rightType);
    return message;
  }

  public String typeMismatchInEquality(MemPred memPred,
				       Type leftType,
				       Type rightType)
  {
    String message = "Type mismatch in equality\n" +
      "\tPredicate: " + format(memPred) + "\n" +
      "\tLHS type: " + formatType(leftType) + "\n" +
      "\tRHS type: " + formatType(rightType);
    return message;
  }

  public String typeMismatchInRelOp(MemPred memPred,
				    Type leftType,
				    Type rightType)
  {
    String message = "Type mismatch in relation\n" +
      "\tPredicate: " + format(memPred) + "\n" +
      "\tType: " + formatType(leftType) + "\n" +
      "\tExpected: " + formatType(rightType);
    return message;
  }

  public String duplicateInBindExpr(BindExpr bindExpr, DeclName declName)
  {
    String message = "Duplicate name in binding expr: " + format(declName);
    return message;
  }

  //converts a Term to a string
  protected String format(Term term)
  {
    StringWriter writer = new StringWriter();
    PrintUtils.printUnicode(term, writer, manager_);
    return writer.toString();
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
    String result = "Unknown location";

    for (Iterator iter = termA.getAnns().iterator(); iter.hasNext(); ) {
      Object next = iter.next();

      if (next instanceof LocAnn) {
	LocAnn locAnn = (LocAnn) next;
	result = "File: " + locAnn.getLoc() + "\n";
	result += "Position: " + locAnn.getLine() + ", " + locAnn.getCol();
	break;
      }
    }

    return result;
  }
}
