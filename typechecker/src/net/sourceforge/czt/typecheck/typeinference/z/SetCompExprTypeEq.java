package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.3
public class SetCompExprTypeEq extends TypeInferenceRule
{
  // list of type subsequents
  private List subsequent_;

  public SetCompExprTypeEq(SectTypeEnv sectTypeEnv,
			   SetCompExpr setCompExpr,
			   TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, setCompExpr);
    typechecker_ = typechecker;
  }

  public Object solve()
    throws TypeException
  {
    SetCompExpr setCompExpr = (SetCompExpr) sequent_.getTerm();

    // type check the schma text part
    SchText schtxt = (SchText) setCompExpr.getSchText().accept(typechecker_);
    // useful?
    //typeEnv_ = typechecker_.getTypeEnv();
    // type check the expr part
    Expr expr = (Expr) setCompExpr.getExpr().accept(typechecker_);
    Type type = typechecker_.getTypeFromAnns(expr);
    // type of the set comprehension expr
    PowerType pt = factory_.createPowerType(type);
    setCompExpr = (SetCompExpr) typechecker_.addAnns(setCompExpr, pt);
    return setCompExpr;
  }
}
