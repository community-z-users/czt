package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Iterator;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.3
public class SetExprTypeEq extends TypeInferenceRule
{
  // list of type subsequents, not used here
  private List subsequent_;

  public SetExprTypeEq(SectTypeEnv sectTypeEnv,
		       SetExpr setExpr,
		       TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, setExpr);
    typechecker_ = typechecker;
  }

  public Object solve()
    throws TypeException
  {
    SetExpr setExpr = (SetExpr) sequent_.getTerm();

    //get the type of the set expr from the anns
    PowerType powerType = (PowerType) typechecker_.getTypeFromAnns(setExpr);

    //get the base type
    Type baseType = powerType.getType();

    List exprs = setExpr.getExpr();
    for (Iterator iter = exprs.iterator(); iter.hasNext(); ) {
      Expr expr = (Expr) iter.next();
      Type exprType = typechecker_.getTypeFromAnns(expr);

      //if the base type is not the same as the next expression
      if (!exprType.equals(baseType)) {
	throw new TypeException(ErrorKind.SETEXPR_MEMBTYPE_NOT_AGREE,
				baseType,
				exprType);
      }
      expr.accept(typechecker_);
    }

    return null;
  }
}
