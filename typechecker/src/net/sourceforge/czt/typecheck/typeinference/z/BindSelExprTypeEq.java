package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.10
public class BindSelExprTypeEq extends TypeInferenceRule
{
  public BindSelExprTypeEq(SectTypeEnv sectTypeEnv,
			   BindSelExpr bindSelExpr,
			   TypeChecker typechecker)
  {
    sequent_ = new Sequent(sectTypeEnv, bindSelExpr);
    typechecker_ = typechecker;
  }

  public Object solve() throws TypeException
  {
    return null;
  }
}
