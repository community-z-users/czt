package net.sourceforge.czt.typecheck.z;

import java.util.List;
import java.io.StringWriter;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.base.ast.*;

import net.sourceforge.czt.typecheck.z.*;

/**
 * An implementation of ErrorFactory that throws exceptions instead of
 * return ErrorAnns
 */
public class ErrorExceptionFactory
  implements ErrorFactory
{
  public ErrorExceptionFactory()
  {
  }

  public void setSection(String sectName)
  {
    //do nothing
  }

  public String getSection()
  {
    return "";
  }

  public ErrorAnn unknownType(Expr expr)
  {
    System.err.println("UNKNOWNTYPE?");
    return null;
  }

  public ErrorAnn undeclaredIdentifier(RefName refName)
  {
    throw new UndeclaredIdentifier();
  }

  public ErrorAnn parametersNotDetermined(Expr expr)
  {
    throw new ParametersNotDetermined();
  }

  public ErrorAnn redeclaredSection(ZSect zSect)
  {
    throw new RedeclaredSection();
  }

  public ErrorAnn redeclaredParent(Parent parent, String sectionName)
  {
    throw new RedeclaredParent();
  }

  public ErrorAnn selfParent(Parent parent)
  {
    throw new SelfParent();
  }

  public ErrorAnn strokeInGiven(DeclName declName)
  {
    throw new StrokeInGiven();
  }

  public ErrorAnn strokeInGen(DeclName declName)
  {
    throw new StrokeInGen();
  }

  public ErrorAnn redeclaredGen(DeclName declName)
  {
    throw new RedeclaredGen();
  }

  public ErrorAnn redeclaredGlobalName(DeclName declName)
  {
    throw new RedeclaredGlobalName();
  }

  public ErrorAnn nonSetInFreeType(Expr expr, Type type)
  {
    throw new NonSetInFreeType();
  }

  public ErrorAnn nonSetInDecl(Expr expr, Type type)
  {
    throw new NonSetInDecl();
  }

  public ErrorAnn nonSetInPowerExpr(Expr expr, Type type)
  {
    throw new NonSetInPowerExpr();
  }

  public ErrorAnn nonSetInProdExpr(ProdExpr prodExpr, Type type, int exprPos)
  {
    throw new NonSetInProdExpr();
  }

  public ErrorAnn nonSetInInstantiation(Expr expr, Type type)
  {
    throw new NonSetInInstantiation();
  }

  public ErrorAnn nonSchExprInInclDecl(InclDecl inclDecl, Type type)
  {
    throw new NonSchExprInInclDecl();
  }

  public ErrorAnn nonProdTypeInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                            Type type)
  {
    throw new NonProdTypeInTupleSelExpr();
  }

  public ErrorAnn nonSchExprInThetaExpr(ThetaExpr thetaExpr, Type type)
  {
    throw new NonSchExprInThetaExpr();
  }

  public ErrorAnn nonSchExprInDecorExpr(DecorExpr decorExpr, Type type)
  {
    throw new NonSchExprInDecorExpr();
  }

  public ErrorAnn nonSchExprInHideExpr(HideExpr hideExpr, Type type)
  {
    throw new NonSchExprInHideExpr();
  }

  public ErrorAnn nonSchExprInPreExpr(PreExpr preExpr, Type type)
  {
    throw new NonSchExprInPreExpr();
  }

  public ErrorAnn nonSchExprInRenameExpr(RenameExpr renameExpr, Type type)
  {
    throw new NonSchExprInRenameExpr();
  }

  public ErrorAnn nonSchExprInExprPred(ExprPred exprPred, Type type)
  {
    throw new NonSchExprInExprPred();
  }

  public ErrorAnn duplicateNameInRenameExpr(RenameExpr renameExpr,
                                            RefName refName)
  {
    throw new DuplicateNameInRenameExpr();
  }

  public ErrorAnn typeMismatchInRenameExpr(RenameExpr renameExpr,
                                    Name name,
                                    Type typeA, Type typeB)
  {
    throw new TypeMismatchInRenameExpr();
  }

  public ErrorAnn nonSchExprInSchExpr2(SchExpr2 schExpr2, Type type)
  {
    throw new NonSchExprInSchExpr2();
  }

  public ErrorAnn nonSchExprInQnt1Expr(Qnt1Expr qnt1Expr, Type type)
  {
    throw new NonSchExprInQnt1Expr();
  }

  public ErrorAnn nonSchExprInBindSelExpr(BindSelExpr bindSelExpr, Type type)
  {
    throw new NonSchExprInBindSelExpr();
  }

  public ErrorAnn typeMismatchInSignature(TermA termA,
                                          DeclName declName,
                                          Type lType,
                                          Type rType)
  {
    throw new TypeMismatchInSignature();
  }

  public ErrorAnn nonExistentSelection(BindSelExpr bindSelExpr)
  {
    throw new NonExistentSelection();
  }

  public ErrorAnn nonExistentNameInHideExpr(HideExpr hideExpr, Name name)
  {
    throw new NonExistentNameInHideExpr();
  }

  public ErrorAnn nonFunctionInApplExpr(ApplExpr applExpr, Type type)
  {
    throw new NonFunctionInApplExpr();
  }

  public ErrorAnn indexErrorInTupleSelExpr(TupleSelExpr tupleSelExpr,
                                           ProdType prodType)
  {
    throw new IndexErrorInTupleSelExpr();
  }

  public ErrorAnn typeMismatchInSetExpr(SetExpr setExpr,
                                        Type type,
                                        Type expectedType)
  {
    throw new TypeMismatchInSetExpr();
  }

  public ErrorAnn typeMismatchInCondExpr(CondExpr condExpr,
                                         Type leftType,
                                         Type rightType)
  {
    throw new TypeMismatchInCondExpr();
  }

  public ErrorAnn typeMismatchInApplExpr(ApplExpr applExpr,
                                         Type expected,
                                         Type actual)
  {
    throw new TypeMismatchInApplExpr();
  }

  public ErrorAnn typeMismatchInMemPred(MemPred memPred,
                                        Type leftType,
                                        Type rightType)
  {
    throw new TypeMismatchInMemPred();
  }

  public ErrorAnn typeMismatchInEquality(MemPred memPred,
                                         Type leftType,
                                         Type rightType)
  {
    throw new TypeMismatchInEquality();
  }

  public ErrorAnn typeMismatchInChainRelation(AndPred andPred,
                                              Type firstUnification,
                                              Type secondUnification)
  {
    throw new TypeMismatchInChainRelation();
  }

  public ErrorAnn typeMismatchInRelOp(MemPred memPred,
                                      Type leftType,
                                      Type rightType)
  {
    throw new TypeMismatchInRelOp();
  }

  public ErrorAnn duplicateInBindExpr(BindExpr bindExpr, DeclName declName)
  {
    throw new DuplicateInBindExpr();
  }
}

abstract class TypeErrorException
  extends RuntimeException
{
  public String getMessage()
  {
    String className = this.getClass().getName();
    int index = className.lastIndexOf(".");
    String baseName = className.substring(index + 1, className.length());
    return baseName;
  }
}

class UndeclaredIdentifier
  extends TypeErrorException
{
}

class ParametersNotDetermined
  extends TypeErrorException
{
}

class RedeclaredSection
  extends TypeErrorException
{
}

class RedeclaredParent
  extends TypeErrorException
{
}

class SelfParent
  extends TypeErrorException
{
}

class StrokeInGiven
  extends TypeErrorException
{
}

class StrokeInGen
  extends TypeErrorException
{
}

class RedeclaredGen
  extends TypeErrorException
{
}

class RedeclaredGlobalName
  extends TypeErrorException
{
}

class NonSetInFreeType
  extends TypeErrorException
{
}

class NonSetInDecl
  extends TypeErrorException
{
}

class NonSetInPowerExpr
  extends TypeErrorException
{
}

class NonSetInProdExpr
  extends TypeErrorException
{
}

class NonSetInInstantiation
  extends TypeErrorException
{
}

class NonSchExprInInclDecl
  extends TypeErrorException
{
}

class NonProdTypeInTupleSelExpr
  extends TypeErrorException
{
}

class NonSchExprInThetaExpr
  extends TypeErrorException
{
}

class NonSchExprInDecorExpr
  extends TypeErrorException
{
}

class NonSchExprInHideExpr
  extends TypeErrorException
{
}

class NonSchExprInPreExpr
  extends TypeErrorException
{
}

class NonSchExprInRenameExpr
  extends TypeErrorException
{
}

class NonSchExprInExprPred
  extends TypeErrorException
{
}

class DuplicateNameInRenameExpr
  extends TypeErrorException
{
}

class TypeMismatchInRenameExpr
  extends TypeErrorException
{
}

class NonSchExprInSchExpr2
  extends TypeErrorException
{
}

class NonSchExprInQnt1Expr
  extends TypeErrorException
{
}

class NonSchExprInBindSelExpr
  extends TypeErrorException
{
}

class TypeMismatchInSignature
  extends TypeErrorException
{
}

class NonExistentSelection
  extends TypeErrorException
{
}

class NonExistentNameInHideExpr
  extends TypeErrorException
{
}

class NonFunctionInApplExpr
  extends TypeErrorException
{
}

class IndexErrorInTupleSelExpr
  extends TypeErrorException
{
}

class TypeMismatchInSetExpr
  extends TypeErrorException
{
}

class TypeMismatchInCondExpr
  extends TypeErrorException
{
}

class TypeMismatchInApplExpr
  extends TypeErrorException
{
}

class TypeMismatchInMemPred
  extends TypeErrorException
{
}

class TypeMismatchInEquality
  extends TypeErrorException
{
}

class TypeMismatchInChainRelation
  extends TypeErrorException
{
}

class TypeMismatchInRelOp
  extends TypeErrorException
{
}

class DuplicateInBindExpr
  extends TypeErrorException
{
}
