package net.sourceforge.czt.typecheck.z;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.typecheck.util.typeerror.TypeException;

public interface ErrorFactory
{
  public String unknownType(Expr expr);
  public String redeclaredSection(String sectionName);
  public String redeclaredParent(Parent parent, String sectionName);
  public String selfParent(String sectionName);
  public String strokeInGiven(DeclName declName);
  public String strokeInGen(DeclName declName);
  public String redeclaredGiven(DeclName declName);
  public String redeclaredGen(DeclName declName);
  public String nonSetInFreeType(Expr expr, Type type);
  public String nonSetInDecl(Expr expr, Type type);
  public String nonSetInPowerExpr(Expr expr, Type type);
  public String nonSetInProdExpr(Expr expr, Type type, int position);
  public String nonSchExprInInclDecl(InclDecl inclDecl);
  public String nonProdTypeInTupleSelExpr(TupleSelExpr tupleSelExpr,
					  Type type);
  public String nonSchExprInThetaExpr(ThetaExpr thetaExpr, Type type);
  public String nonSchTypeInBindSelExpr(BindSelExpr bindSelExpr, Type type);
  public String nonExistentSelection(BindSelExpr bindSelExpr, Type type);
  public String nonFunctionInApplExpr(ApplExpr applExpr, Type type);
  public String indexErrorInTupleSelExpr(TupleSelExpr tupleSelExpr,
					 ProdType prodType);
  public String typeMismatchInSetExpr(Expr expr, Type type, Type expectedType);
  public String typeMismatchInCondExpr(CondExpr condExpr, 
				       Type leftType,
				       Type rightType);
  public String typeMismatchInApplExpr(ApplExpr applExpr, 
				       Type expected, Type actual);
  public String typeMismatchInMemPred(MemPred memPred,
				      Type leftType, Type rightType);
  public String typeMismatchInEquality(MemPred memPred,
				       Type leftType, Type rightType);
  public String typeMismatchInRelOp(MemPred memPred,
				    Type leftType, Type rightType);
  public String duplicateInBindExpr(BindExpr bindExpr, DeclName declName);
}
