package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for SchemaType that hides VariableSignature
 * instances if they have a value.
 */
public class SchemaTypeImpl
  extends Type2Impl
  implements SchemaType
{
  protected SchemaTypeImpl(SchemaType schemaType)
  {
    super(schemaType);
  }

  public void setSignature(Signature signature)
  {
    SchemaType schemaType = (SchemaType) term_;
    schemaType.setSignature(signature);
  }

  public Signature getSignature()
  {
    SchemaType schemaType = (SchemaType) term_;
    Signature result = schemaType.getSignature();
    if (result instanceof VariableSignature) {
      VariableSignature vSig = (VariableSignature) result;
      if (vSig.getValue() != null) {
        result = vSig.getValue();
      }
    }
    return result;
  }

  public String toString()
  {
    SchemaType schemaType = (SchemaType) term_;
    return schemaType.toString();
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof SchemaType) {
      SchemaType schemaType = (SchemaType) obj;
      return getSignature().equals(schemaType.getSignature());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "SchemaTypeImpl".hashCode();
    if (getSignature() != null) {
      hashCode += constant * getSignature().hashCode();
    }
    return hashCode;
  }
}
