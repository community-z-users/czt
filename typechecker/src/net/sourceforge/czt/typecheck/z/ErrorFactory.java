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
  ErrorAnn parameterMismatch(RefExpr refExpr, int paramLength);
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
  ErrorAnn nonSchExprInHideExpr(HideExpr hideExpr, Type type);
  ErrorAnn nonSchExprInPreExpr(PreExpr preExpr, Type type);
  ErrorAnn nonSchExprInSchExpr2(SchExpr2 schExpr2, Type type);
  ErrorAnn nonSchExprInQnt1Expr(Qnt1Expr qnt1Expr, Type type);
  ErrorAnn nonSchExprInExprPred(ExprPred exprPred, Type type);
  ErrorAnn nonSchExprInRenameExpr(RenameExpr renameExpr, Type type);
  ErrorAnn duplicateNameInRenameExpr(RenameExpr renameExpr,
                                     RefName refName);
  ErrorAnn typeMismatchInSignature(TermA termA, DeclName declName,
                                   Type lType, Type rType);
  ErrorAnn nonBindingInBindSelExpr(BindSelExpr bindSelExpr, Type type);
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
