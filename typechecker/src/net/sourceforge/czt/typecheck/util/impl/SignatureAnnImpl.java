package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.z.ast.*;

/**
 * An implementation for SignatureAnn that hides VariableSignature
 * instances if they have a value.
 */
public class SignatureAnnImpl
  extends TermImpl
  implements SignatureAnn
{
  protected SignatureAnnImpl(SignatureAnn signatureAnn)
  {
    super(signatureAnn);
  }

  public void setSignature(Signature signature)
  {
    SignatureAnn signatureAnn = (SignatureAnn) term_;
    signatureAnn.setSignature(signature);
  }

  public Signature getSignature()
  {
    SignatureAnn signatureAnn = (SignatureAnn) term_;
    Signature result = signatureAnn.getSignature();
    if (result instanceof VariableSignature) {
      VariableSignature vSignature = (VariableSignature) result;
      if (vSignature.getValue() != null) {
        result = vSignature.getValue();
      }
    }
    return result;
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof SignatureAnn) {
      SignatureAnn signatureAnn = (SignatureAnn) obj;
      return getSignature().equals(signatureAnn.getSignature());
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "SignatureAnnImpl".hashCode();
    if (getSignature() != null) {
      hashCode += constant * getSignature().hashCode();
    }
    return hashCode;
  }
}
