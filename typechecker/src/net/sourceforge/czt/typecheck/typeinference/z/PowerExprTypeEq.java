package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.3
public class PowerExprTypeEq extends TypeInferenceRule
{
  public PowerExprTypeEq(SectTypeEnv sectTypeEnv,
			 PowerExpr powerExpr,
			 TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, powerExpr);
    typechecker_ = typechecker;
  }

  public Object solve()
    throws TypeException
  {
    PowerExpr powerExpr = (PowerExpr) sequent_.getTerm();
    Expr expr = powerExpr.getExpr();
    expr.accept(typechecker_);

    Type type = typechecker_.getTypeFromAnns(expr);
    if (! (type instanceof PowerType)) {
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, expr);
    }

    return null;
  }
}
