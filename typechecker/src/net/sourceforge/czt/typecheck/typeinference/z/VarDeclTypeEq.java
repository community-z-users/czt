package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.z.TypeChecker;

// 13.2.6.3
public class VarDeclTypeEq extends TypeInferenceRule
{
  private Sequent subsequent_;

  public VarDeclTypeEq(SectTypeEnv sectTypeEnv,
		       VarDecl varDecl,
		       TypeChecker typechecker)
  {
    subsequent_ = new Sequent(sectTypeEnv, varDecl.getExpr());
    sequent_ = new Sequent(sectTypeEnv, varDecl);
    typechecker_ = typechecker;
  }

  // this method won't throw exceptions
  public Object solve() throws TypeException
  {
    VarDecl varDecl = (VarDecl) sequent_.getTerm();

    //visit the expression
    Expr expr = varDecl.getExpr();
    expr.accept(typechecker_);
    
    Type type = typechecker_.getTypeFromAnns(expr);
    if (! (type instanceof PowerType)) {
      String message = "Set expression needed in declaration";
      throw new TypeException(ErrorKind.POWERTYPE_NEEDED, expr, message);
    }

    return null;
  }
}
