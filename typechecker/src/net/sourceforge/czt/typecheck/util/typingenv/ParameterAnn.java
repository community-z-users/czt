package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.base.ast.Term;

/**
 * An annotation for recording the generic parameters associated with
 * a generic operator name
 */
public class ParameterAnn
{
  /** The parameters */
  protected List parameters_;

  public ParameterAnn(List parameters)
  {
    parameters_ = parameters;
  }

  public void setParameters(List parameters)
  {
    parameters_ = parameters;
  }

  public List getParameters()
  {
    return parameters_;
  }
}
