package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.3
public class SetCompExprTypeEq implements TypeInferenceRule
{
  // list of type subsequents
  // 2 items
  private List subsequent_;
  private Sequent sequent_;

  private TypeChecker checker_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv_;

  public SetCompExprTypeEq(TypeEnvInt env, SetCompExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    factory_ = checker_.getFactory();
  }

  public Object solve()
    throws TypeException
  {
    SetCompExpr scexpr = (SetCompExpr) sequent_.getTerm();

    // type check the schma text part
    SchText schtxt = (SchText) scexpr.getSchText().accept(checker_);
    // useful?
    //typeEnv_ = checker_.getTypeEnv();
    // type check the expr part
    Expr expr = (Expr) scexpr.getExpr().accept(checker_);
    Type type = checker_.getTypeFromAnns(expr);
    // type of the set comprehension expr
    PowerType pt = factory_.createPowerType(type);
    scexpr = (SetCompExpr) checker_.addAnns(scexpr, pt);
    return scexpr;
  }
}
