package net.sourceforge.czt.typecheck.z;

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
    String message
      = "Type of " + format(expr) + " cannot be inferred";
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


  //converts a Term to a string
  protected String format(Term term)
  {
    StringWriter writer = new StringWriter();
    PrintUtils.printUnicode(term, writer, manager_);
    return writer.toString();
  }

  protected String formatType(Type type)
  {
    TypeFormatter formatter = new TypeFormatter();
    Expr expr = (Expr) type.accept(formatter);
    return format(expr);
  }
}
