package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.3
public class SetExprTypeEq implements TypeInferenceRule
{
  // list of type subsequents, not used here
  private List subsequent_;
  private Sequent sequent_;

  private TypeChecker checker_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv_;

  public SetExprTypeEq(TypeEnvInt env, SetExpr term, TypeChecker checker)
  {
    sequent_ = new Sequent(env, term);
    checker_ = checker;
    factory_ = checker_.getFactory();
    typeEnv_ = env;
  }

  public Object solve()
    throws TypeException
  {
    SetExpr stexpr = (SetExpr) sequent_.getTerm();
    List exprs = stexpr.getExpr();
    int size = exprs.size();
    // type of set extension expr should be a power type of some type
    PowerType pt = factory_.createPowerType();
    // type of the member exprs
    Type exprType = null;
    if (size == 0) {
      exprType = new VariableType();
    }
    else {
      Expr expr = null;
      Expr firstExpr = null;
      boolean ok = true;
      firstExpr = (Expr) ((Expr) exprs.get(0)).accept(checker_);
      Type firstType = checker_.getTypeFromAnns(firstExpr);
      if (firstType instanceof VariableType) ok = false;
      for (int i = 1; (ok && i < size); i++) {
        try {
          expr = (Expr) ((Expr) exprs.get(i)).accept(checker_);
          exprType = (Type) checker_.getTypeFromAnns(expr);
          if (! (((PowerType) firstType).getType() instanceof VariableType))
            ok = TypeChecker.unify(firstType, exprType);
          if (! ok) {
            throw new TypeException(ErrorKind.SETEXPR_MEMBTYPE_NOT_AGREE,
                                    firstType,
                                    exprType);
          }
        }
        catch (TypeException e) {
          Type tmpType = new VariableType();
          exprType = factory_.createPowerType(tmpType);
          e.printStackTrace();
          ok = false;
        }
      }
    }
    pt.setType(exprType);
    stexpr = (SetExpr) checker_.addAnns(stexpr, pt);
    return stexpr;
  }
}
