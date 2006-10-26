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
package net.sourceforge.czt.typecheck.oz.impl;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.typecheck.z.impl.*;

/**
 * An implementation for NameSignaturePair that hides
 * VariableSignature instances if they have a value.
 */
public class NameSignaturePairImpl
  extends TermImpl
  implements NameSignaturePair
{
  protected NameSignaturePairImpl(NameSignaturePair nameSignaturePair)
  {
    super(nameSignaturePair);
  }

  public void setName(Name declName)
  {
    NameSignaturePair nameSignaturePair = (NameSignaturePair) term_;
    nameSignaturePair.setName(declName);
  }

  public Name getName()
  {
    NameSignaturePair nameSignaturePair = (NameSignaturePair) term_;
    return nameSignaturePair.getName();
  }

  public ZName getZName()
  {
    NameSignaturePair nameSignaturePair = (NameSignaturePair) term_;
    return nameSignaturePair.getZName();
  }

  public void setSignature(Signature signature)
  {
    NameSignaturePair nameSignaturePair = (NameSignaturePair) term_;
    nameSignaturePair.setSignature(signature);
  }

  public Signature getSignature()
  {
    NameSignaturePair nameSignaturePair = (NameSignaturePair) term_;
    Signature result = nameSignaturePair.getSignature();
    if (result instanceof VariableSignature) {
      VariableSignature vSignature = (VariableSignature) result;
      if (vSignature.getValue() != null) {
        result = vSignature.getValue();
      }
    }
    return result;
  }

  public NameSignaturePairImpl create(Object [] args)
  {
    NameSignaturePair pair = (NameSignaturePair) term_.create(args);
    NameSignaturePairImpl result = new NameSignaturePairImpl(pair);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof NameSignaturePairVisitor) {
      NameSignaturePairVisitor<R> visitor = (NameSignaturePairVisitor<R>) v;
      return visitor.visitNameSignaturePair(this);
    }
    return super.accept(v);
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof NameSignaturePair) {
      NameSignaturePair pair = (NameSignaturePair) obj;
      if (!getName().equals(pair.getName()) ||
          !getSignature().equals(pair.getSignature())) {
        return false;
      }
      return true;
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "NameSignaturePairImpl".hashCode();
    if (getName() != null) {
      hashCode += constant * getName().hashCode();
    }
    if (getSignature() != null) {
      hashCode += constant * getSignature().hashCode();
    }
    return hashCode;
  }
}
