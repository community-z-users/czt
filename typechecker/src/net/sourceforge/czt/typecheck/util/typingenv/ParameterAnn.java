package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.Type2;

import net.sourceforge.czt.typecheck.util.impl.*;

/**
 * An annotation for recording a list of annotations associated with
 * an expression.
 */
public class ParameterAnn
{
  /** The parameters. */
  protected List parameters_;

  public ParameterAnn(List anns)
  {
    parameters_ = anns;
  }

  public List getParameters()
  {
    return parameters_;
  }
}
