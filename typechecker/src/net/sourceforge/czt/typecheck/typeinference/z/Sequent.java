package net.sourceforge.czt.typecheck.typeinference.z;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;

public class Sequent
{
  //accomodate variable env
  private SectTypeEnv sectTypeEnv_;
  private TermA termA_;

  public Sequent (SectTypeEnv sectTypeEnv, TermA termA)
  {
    sectTypeEnv_ = sectTypeEnv;
    termA_ = termA;
  }

  public SectTypeEnv getSectTypeEnv()
  {
    return sectTypeEnv_;
  }

  public TypeEnvInt getTypeEnv()
  {
    return null;
  }

  public TermA getTerm()
  {
    return termA_;
  }
}
