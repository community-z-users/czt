package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.3
public class PowerExprTypeEq extends TypeInferenceRule
{
  private ZFactory factory_;

  public PowerExprTypeEq(TypeEnvInt env, PowerExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    factory_ = checker_.getFactory();
  }

  public Object solve()
    throws TypeException
  {
    PowerExpr term = (PowerExpr) sequent_.getTerm();
    Expr expr = term.getExpr();
    expr = (Expr) expr.accept(checker_);
    Type type = checker_.getTypeFromAnns(expr);
    if (! (type instanceof PowerType)) {
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, expr);
    }
    PowerType pt = factory_.createPowerType(type);
    term = (PowerExpr) checker_.addAnns(term, pt);
    return term;
  }
}
