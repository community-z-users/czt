package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.11
public class ApplExprTypeEq extends TypeInferenceRule
{
  public ApplExprTypeEq(SectTypeEnv sectTypeEnv, 
			ApplExpr applExpr, 
			TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, applExpr);
    typechecker_ = typechecker;
  }

  public Object solve() throws TypeException
  {
    /*
    ApplExpr term = (ApplExpr) sequent_.getTerm();
    // get mixfix
    // what if mixfix == true???
    boolean mixfix = false;
    Boolean mix = term.getMixfix();
    try {
      mixfix = mix.booleanValue();
    }
    catch (NullPointerException e) {
      mixfix = false;
    }
    Expr left = (Expr) term.getLeftExpr().accept(typechecker_);
    Expr right = (Expr) term.getRightExpr().accept(typechecker_);
    Type leftT = typechecker_.getTypeFromAnns(left);
    // maybe this is the place to consider type unification?
    // say, leftT is of VariableType...
    // so maybe delay all these type testing to a later stage...
    if (! (leftT instanceof PowerType)) {
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, leftT);
    }
    Type prodT = ((PowerType) leftT).getType();
    if (! (prodT instanceof ProdType)) {
      throw new TypeException(ErrorKind.PRODTYPE_REQUIRED, prodT);
    }
    List types = ((ProdType) prodT).getType();
    Type rightT = typechecker_.getTypeFromAnns(right);
    if (types.size() != 2) {
      throw new TypeException(ErrorKind.TWO_COMPONENT_NEEDED, prodT);
    }
    Type first = (Type) types.get(0);
    if (! TypeChecker.unify(rightT, first)) {
      throw new TypeException(ErrorKind.APPLEXPR_TYPES_DO_NOT_AGREE,
                              rightT,
                              first);
    }
    Type second = (Type) types.get(1);
    term = (ApplExpr) typechecker_.addAnns(term, second);
    */
    return null;
  }
}
