package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.12
public class MuExprTypeEq extends TypeInferenceRule
{
  private ZFactory factory_;

  public MuExprTypeEq(TypeEnvInt env, MuExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    factory_ = checker_.getFactory();
  }

  // why should the expr be optional?
  public Object solve() throws TypeException
  {
    MuExpr term = (MuExpr) sequent_.getTerm();
    TypeEnvInt typeEnv = sequent_.getTypeEnv();
    typeEnv.enterScope();
    SchText schtext = (SchText) term.getSchText().accept(checker_);
    // now typeEnv should contain decls from schtext
    Expr expr = (Expr) term.getExpr().accept(checker_);
    Type type = checker_.getTypeFromAnns(expr);
    term = (MuExpr) checker_.addAnns(term, type);
    typeEnv.exitScope();
    return term;
  }
}
