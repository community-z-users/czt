package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.typecheck.util.typeerror.TypeException;

interface TypeInferenceRule
{
  Object solve() throws TypeException;
}
