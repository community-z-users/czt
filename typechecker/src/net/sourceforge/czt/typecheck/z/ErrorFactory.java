package net.sourceforge.czt.typecheck.z;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A factory interface for type checking error message.
 */
public interface ErrorFactory
{
  String unknownType(Expr expr);
  String redeclaredSection(String sectionName);
  String redeclaredParent(Parent parent, String sectionName);
  String selfParent(String sectionName);
  String strokeInGiven(DeclName declName);
  String strokeInGen(DeclName declName);
  String redeclaredGiven(DeclName declName);
  String redeclaredGen(DeclName declName);
  String nonSetInFreeType(Expr expr, Type type);
  String nonSetInDecl(Expr expr, Type type);
  String nonSetInPowerExpr(Expr expr, Type type);
  String nonSetInProdExpr(Expr expr, Type type, int position);
  String nonSchExprInInclDecl(InclDecl inclDecl);
  String nonProdTypeInTupleSelExpr(TupleSelExpr tupleSelExpr,
				   Type type);
  String nonSchExprInThetaExpr(ThetaExpr thetaExpr, Type type);
  String nonSchExprInQnt1Expr(Qnt1Expr qnt1Expr, Type type);
  String nonSchTypeInBindSelExpr(BindSelExpr bindSelExpr, Type type);
  String nonExistentSelection(BindSelExpr bindSelExpr, Type type);
  String nonFunctionInApplExpr(ApplExpr applExpr, Type type);
  String indexErrorInTupleSelExpr(TupleSelExpr tupleSelExpr,
				  ProdType prodType);
  String typeMismatchInSetExpr(Expr expr, Type type, Type expectedType);
  String typeMismatchInCondExpr(CondExpr condExpr,
				Type leftType,
				Type rightType);
  String typeMismatchInApplExpr(ApplExpr applExpr,
				Type expected,
				Type actual);
  String typeMismatchInMemPred(MemPred memPred,
			       Type leftType,
			       Type rightType);
  String typeMismatchInEquality(MemPred memPred,
				Type leftType,
				Type rightType);
  String typeMismatchInRelOp(MemPred memPred,
			     Type leftType,
			     Type rightType);
  String duplicateInBindExpr(BindExpr bindExpr, DeclName declName);
}
