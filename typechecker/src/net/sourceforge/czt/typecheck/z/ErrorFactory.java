package net.sourceforge.czt.typecheck.z;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A factory interface for type checking error message.
 */
public interface ErrorFactory
{
  ErrorAnn unknownType(Expr expr);
  ErrorAnn undeclaredIdentifier(RefExpr refExpr);
  ErrorAnn parametersNotDetermined(Expr expr);
  ErrorAnn redeclaredSection(ZSect zSect);
  ErrorAnn redeclaredParent(Parent parent, String sectionName);
  ErrorAnn selfParent(Parent parent);
  ErrorAnn strokeInGiven(DeclName declName);
  ErrorAnn strokeInGen(DeclName declName);
  ErrorAnn redeclaredGiven(DeclName declName);
  ErrorAnn redeclaredGen(DeclName declName);
  ErrorAnn nonSetInFreeType(Expr expr, Type type);
  ErrorAnn nonSetInDecl(Expr expr, Type type);
  ErrorAnn nonSetInPowerExpr(Expr expr, Type type);
  ErrorAnn nonSetInProdExpr(Expr expr, Type type, int position);
  ErrorAnn nonSetInInstantiation(Expr expr, Type type);
  ErrorAnn nonSchExprInInclDecl(InclDecl inclDecl, Type type);
  ErrorAnn nonProdTypeInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                   Type type);
  ErrorAnn nonSchExprInThetaExpr(ThetaExpr thetaExpr, Type type);
  ErrorAnn nonSchExprInQnt1Expr(Qnt1Expr qnt1Expr, Type type);
  ErrorAnn nonSchTypeInBindSelExpr(BindSelExpr bindSelExpr, Type type);
  ErrorAnn nonExistentSelection(BindSelExpr bindSelExpr);
  ErrorAnn nonFunctionInApplExpr(ApplExpr applExpr, Type type);
  ErrorAnn indexErrorInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                  ProdType prodType);
  ErrorAnn typeMismatchInSetExpr(Expr expr, Type type, Type expectedType);
  ErrorAnn typeMismatchInCondExpr(CondExpr condExpr,
                                Type leftType,
                                Type rightType);
  ErrorAnn typeMismatchInApplExpr(ApplExpr applExpr,
                                Type expected,
                                Type actual);
  ErrorAnn typeMismatchInMemPred(MemPred memPred,
                               Type leftType,
                               Type rightType);
  ErrorAnn typeMismatchInEquality(MemPred memPred,
                                  Type leftType,
                                  Type rightType);
  ErrorAnn typeMismatchInChainRelation(AndPred andPred,
                                       Type firstUnification,
                                       Type secondUnification);
  ErrorAnn typeMismatchInRelOp(MemPred memPred,
                             Type leftType,
                             Type rightType);
  ErrorAnn duplicateInBindExpr(BindExpr bindExpr, DeclName declName);
}
