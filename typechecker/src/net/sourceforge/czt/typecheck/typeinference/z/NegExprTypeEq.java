package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.15
public class NegExprTypeEq implements TypeInferenceRule
{
  private Sequent sequent_;

  private TypeChecker checker_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv_;

  public NegExprTypeEq(TypeEnvInt env, NegExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    typeEnv_ = checker_.getTypeEnv();
    factory_ = checker_.getFactory();
  }

  // why should the expr be optional?
  public Object solve() throws TypeException
  {
    NegExpr term = (NegExpr) sequent_.getTerm();
    Expr expr = (Expr) term.getExpr().accept(checker_);
    Type type = checker_.getTypeFromAnns(expr);
    if (! (type instanceof PowerType)) {
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, type);
    }
    Type innerType = ((PowerType) type).getType();
    if (! (innerType instanceof SchemaType)) {
      throw new TypeException(ErrorKind.SCHEMATYPE_NEEDED, innerType);
    }
    term = (NegExpr) checker_.addAnns(term, type);
    return term;
  }
}
