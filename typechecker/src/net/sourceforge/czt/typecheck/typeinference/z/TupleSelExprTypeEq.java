package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.7
public class TupleSelExprTypeEq implements TypeInferenceRule
{
  private Sequent sequent_;

  private TypeChecker checker_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv_;

  public TupleSelExprTypeEq(TypeEnvInt env, TupleSelExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    factory_ = checker_.getFactory();
  }

  public Object solve() throws TypeException
  {
    TupleSelExpr term = (TupleSelExpr) sequent_.getTerm();
    Expr expr = (Expr) term.getExpr().accept(checker_);
    Type type = checker_.getTypeFromAnns(expr);
    int which = term.getSelect().intValue();
    if (! (type instanceof ProdType)) {
      throw new TypeException(ErrorKind.PRODTYPE_REQUIRED, term);
    }
    List types = ((ProdType) type).getType();
    if (which > types.size()) {
      throw new TypeException(ErrorKind.INVALID_TUPLESELEXPR_SELECT, term);
    }
    Type resultType = (Type) types.get(which - 1);
    return resultType;
  }
}

