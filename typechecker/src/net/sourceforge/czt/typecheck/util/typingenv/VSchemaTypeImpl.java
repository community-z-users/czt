package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.SchemaTypeImpl;

/**
 * An implementation for SchemaType that hides VariableSignature
 * instances if they have a value.
 */
public class VSchemaTypeImpl
  extends SchemaTypeImpl
{
  protected VSchemaTypeImpl()
  {
    super();
  }

  public Signature getSignature()
  {
    Signature result = super.getSignature();

    if (result instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) result;

      if (vSig.getValue() != null) {
        result = vSig.getValue();
      }
    }
    return result;
  }
}
