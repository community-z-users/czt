package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.6
public class TupleExprTypeEq extends TypeInferenceRule
{
  private ZFactory factory_;

  public TupleExprTypeEq(TypeEnvInt env, TupleExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    factory_ = checker_.getFactory();
  }

  // need to check tuple expr has at least 2 elements
  public Object solve() throws TypeException
  {
    TupleExpr term = (TupleExpr) sequent_.getTerm();
    List exprs = term.getExpr();
    if (exprs.size() < 2) {
      throw new TypeException(ErrorKind.TUPLEEXPR_LESSTHAN_2, term);
    }
    // type of term should be a cartesian product type
    ProdType prodt = factory_.createProdType();
    List types = prodt.getType();
    Expr expr = null;
    Type type = null;
    for (int i = 0; i < exprs.size(); i++) {
      expr = (Expr) ((Expr) exprs.get(i)).accept(checker_);
      // should overwrite?
      exprs.set(i, expr);
      type = checker_.getTypeFromAnns(expr);
      types.add(type);
    }
    term = (TupleExpr) checker_.addAnns(term, prodt);
    return term;
  }
}
