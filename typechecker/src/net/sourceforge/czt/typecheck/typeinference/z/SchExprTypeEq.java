package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.14
public class SchExprTypeEq extends TypeInferenceRule
{
  public SchExprTypeEq(SectTypeEnv sectTypeEnv,
		       SchExpr schExpr,
		       TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, schExpr);
    typechecker_ = typechecker;
  }

  // why should the expr be optional?
  public Object solve() throws TypeException
  {
    SchExpr schExpr = (SchExpr) sequent_.getTerm();
    TypeEnvInt typeEnv = sequent_.getTypeEnv();
    typeEnv.enterScope();
    SchText schtext = (SchText) schExpr.getSchText().accept(typechecker_);
    Type type = typechecker_.getTypeFromAnns(schtext);
    schExpr = (SchExpr) typechecker_.addAnns(schExpr, type);
    typeEnv.exitScope();
    return schExpr;
  }
}
