package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

/**
 * An annotation for recording the types associated with a reference
 * expression.
 */
public class ParameterAnn
{
  /** The parameters. */
  protected List parameters_;

  public ParameterAnn(List types)
  {
    parameters_ = types;
  }

  public List getParameters()
  {
    return parameters_;
  }
}
