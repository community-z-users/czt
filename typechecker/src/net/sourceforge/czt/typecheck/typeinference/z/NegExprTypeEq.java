package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.15
public class NegExprTypeEq extends TypeInferenceRule
{
  public NegExprTypeEq(SectTypeEnv sectTypeEnv,
		       NegExpr negExpr,
		       TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, negExpr);
    typechecker_ = typechecker;
  }

  // why should the expr be optional?
  public Object solve() throws TypeException
  {
    NegExpr negExpr = (NegExpr) sequent_.getTerm();
    Expr expr = (Expr) negExpr.getExpr().accept(typechecker_);
    Type type = typechecker_.getTypeFromAnns(expr);
    if (! (type instanceof PowerType)) {
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, type);
    }
    Type innerType = ((PowerType) type).getType();
    if (! (innerType instanceof SchemaType)) {
      throw new TypeException(ErrorKind.SCHEMATYPE_NEEDED, innerType);
    }
    negExpr = (NegExpr) typechecker_.addAnns(negExpr, type);
    return negExpr;
  }
}
