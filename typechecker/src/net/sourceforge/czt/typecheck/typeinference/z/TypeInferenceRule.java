package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.typecheck.util.typeerror.TypeException;
import net.sourceforge.czt.typecheck.z.TypeChecker;

public abstract class TypeInferenceRule
{
  /** The sequent for this rule */
  protected Sequent sequent_;

  /** The typechecker that creates this rule */
  protected TypeChecker checker_;

  abstract Object solve() throws TypeException;
}
