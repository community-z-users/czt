package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.Type2;

import net.sourceforge.czt.typecheck.util.impl.*;

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
    List result = parameters_;

    for (int i = 0; i < result.size(); i++) {
      Type2 type = (Type2) result.get(i);
      if (type instanceof VariableType) {
        VariableType vType = (VariableType) type;

        if (vType.getValue() != null) {
          result.set(i, vType.getValue());
        }
      }
    }

    return result;
  }
}
