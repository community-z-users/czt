package net.sourceforge.czt.typecheck.z;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.typecheck.util.typeerror.TypeException;

public interface ErrorFactory
{
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
  public String typeMismatchInSetExpr(Expr expr, Type type, Type expectedType);
  public String typeMismatchInCondExpr(CondExpr condExpr, 
				       Type leftType,
				       Type rightType);
}
