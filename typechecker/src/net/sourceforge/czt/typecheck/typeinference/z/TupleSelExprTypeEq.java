package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.7
public class TupleSelExprTypeEq extends TypeInferenceRule
{
  public TupleSelExprTypeEq(SectTypeEnv sectTypeEnv,
			    TupleSelExpr tupleSelExpr,
			    TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, tupleSelExpr);
    typechecker_ = typechecker;
  }

  public Object solve() throws TypeException
  {
    TupleSelExpr tupleSelExpr = (TupleSelExpr) sequent_.getTerm();
    Expr expr = (Expr) tupleSelExpr.getExpr().accept(typechecker_);
    Type type = typechecker_.getTypeFromAnns(expr);
    int which = tupleSelExpr.getSelect().intValue();
    if (! (type instanceof ProdType)) {
      throw new TypeException(ErrorKind.PRODTYPE_REQUIRED, tupleSelExpr);
    }
    List types = ((ProdType) type).getType();
    if (which > types.size()) {
      throw new TypeException(ErrorKind.INVALID_TUPLESELEXPR_SELECT, tupleSelExpr);
    }
    Type resultType = (Type) types.get(which - 1);
    return resultType;
  }
}

