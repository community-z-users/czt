package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.12
public class MuExprTypeEq extends TypeInferenceRule
{
  public MuExprTypeEq(SectTypeEnv sectTypeEnv,
		      MuExpr muExpr,
		      TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, muExpr);
    typechecker_ = typechecker;
  }

  // why should the expr be optional?
  public Object solve() throws TypeException
  {
    MuExpr muExpr = (MuExpr) sequent_.getTerm();
    TypeEnvInt typeEnv = sequent_.getTypeEnv();
    typeEnv.enterScope();
    SchText schtext = (SchText) muExpr.getSchText().accept(typechecker_);
    // now typeEnv should contain decls from schtext
    Expr expr = (Expr) muExpr.getExpr().accept(typechecker_);
    Type type = typechecker_.getTypeFromAnns(expr);
    muExpr = (MuExpr) typechecker_.addAnns(muExpr, type);
    typeEnv.exitScope();
    return muExpr;
  }
}
