package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.14
public class SchExprTypeEq implements TypeInferenceRule
{
  private Sequent sequent_;

  private TypeChecker checker_;

  private ZFactory factory_;
  private TypeEnvInt typeEnv_;

  public SchExprTypeEq(TypeEnvInt env, SchExpr term, TypeChecker tc)
  {
    sequent_ = new Sequent(env, term);
    checker_ = tc;
    typeEnv_ = checker_.getTypeEnv();
    factory_ = checker_.getFactory();
  }

  // why should the expr be optional?
  public Object solve() throws TypeException
  {
    SchExpr term = (SchExpr) sequent_.getTerm();
    typeEnv_.enterScope();
    SchText schtext = (SchText) term.getSchText().accept(checker_);
    Type type = checker_.getTypeFromAnns(schtext);
    term = (SchExpr) checker_.addAnns(term, type);
    typeEnv_.exitScope();
    return term;
  }
}
