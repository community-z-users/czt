package net.sourceforge.czt.typecheck.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A factory interface for type checking error message.
 */
public interface ErrorFactory
{
  void setSection(String sectName);
  String getSection();
  ErrorAnn unknownType(Expr expr);
  ErrorAnn undeclaredIdentifier(RefName refName);
  ErrorAnn parametersNotDetermined(Expr expr);
  ErrorAnn redeclaredSection(ZSect zSect);
  ErrorAnn redeclaredParent(Parent parent, String sectionName);
  ErrorAnn selfParent(Parent parent);
  ErrorAnn strokeInGiven(DeclName declName);
  ErrorAnn strokeInGen(DeclName declName);
  ErrorAnn redeclaredGen(DeclName declName);
  ErrorAnn redeclaredGlobalName(DeclName declName);
  ErrorAnn nonSetInFreeType(Expr expr, Type type);
  ErrorAnn nonSetInDecl(Expr expr, Type type);
  ErrorAnn nonSetInPowerExpr(Expr expr, Type type);
  ErrorAnn nonSetInProdExpr(ProdExpr prodExpr, Type type, int position);
  ErrorAnn nonSetInInstantiation(Expr expr, Type type);
  ErrorAnn nonSchExprInInclDecl(InclDecl inclDecl, Type type);
  ErrorAnn nonProdTypeInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                   Type type);
  ErrorAnn nonSchExprInThetaExpr(ThetaExpr thetaExpr, Type type);
  ErrorAnn nonSchExprInDecorExpr(DecorExpr decorExpr, Type type);
  ErrorAnn nonSchExprInBindSelExpr(BindSelExpr bindSelExpr, Type type);
  ErrorAnn nonSchExprInHideExpr(HideExpr hideExpr, Type type);
  ErrorAnn nonSchExprInPreExpr(PreExpr preExpr, Type type);
  ErrorAnn nonSchExprInSchExpr2(SchExpr2 schExpr2, Type type);
  ErrorAnn nonSchExprInQnt1Expr(Qnt1Expr qnt1Expr, Type type);
  ErrorAnn nonSchExprInExprPred(ExprPred exprPred, Type type);
  ErrorAnn nonSchExprInRenameExpr(RenameExpr renameExpr, Type type);
  ErrorAnn duplicateNameInRenameExpr(RenameExpr renameExpr,
                                     RefName refName);
  ErrorAnn typeMismatchInRenameExpr(RenameExpr renameExpr,
                                    Name name, Type typeA, Type typeB);
  ErrorAnn typeMismatchInSignature(TermA termA, DeclName declName,
                                   Type lType, Type rType);
  ErrorAnn nonExistentSelection(BindSelExpr bindSelExpr);
  ErrorAnn nonExistentNameInHideExpr(HideExpr hideExpr, Name name);
  ErrorAnn nonFunctionInApplExpr(ApplExpr applExpr, Type type);
  ErrorAnn indexErrorInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                  ProdType prodType);
  ErrorAnn typeMismatchInSetExpr(SetExpr setExpr, Type type,
                                 Type expectedType);
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
