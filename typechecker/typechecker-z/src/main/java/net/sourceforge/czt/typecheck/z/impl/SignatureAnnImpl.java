/*
  Copyright (C) 2004 Tim Miller
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.typecheck.z.impl;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * An implementation for SignatureAnn that hides VariableSignature
 * instances if they have a value.
 */
public class SignatureAnnImpl
  extends AnnImpl
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

  public Object[] getChildren()
  {
    Object[] erg = { getSignature() };
    return erg;
  }

  public SignatureAnnImpl create(Object [] args)
  {
    SignatureAnn signatureAnn = (SignatureAnn) term_.create(args);
    SignatureAnnImpl result = new SignatureAnnImpl(signatureAnn);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof SignatureAnnVisitor) {
      SignatureAnnVisitor<R> visitor = (SignatureAnnVisitor<R>) v;
      return visitor.visitSignatureAnn(this);
    }
    return super.accept(v);
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
