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
 * An implementation for Ann that hides VariableType and
 * VariableSignature instances if they have a value.
 */
public class AnnImpl
  extends TermImpl
  implements Ann
{
  protected AnnImpl(Ann ann)
  {
    super(ann);
  }

  public AnnImpl create(Object [] args)
  {
    Ann ann = (Ann) term_.create(args);
    AnnImpl result = new AnnImpl(ann);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof AnnVisitor) {
      AnnVisitor<R> visitor = (AnnVisitor<R>) v;
      return visitor.visitAnn(this);
    }
    return super.accept(v);
  }

  public boolean equals(Object obj)
  {
    if (obj != null && obj instanceof Ann) {
      if (this.getClass().equals(obj.getClass()) && super.equals(obj)) {
       // AnnImpl object = (AnnImpl) obj;
        return true;
      }
    }
    return false;
  }

  public int hashCode()
  {
   // final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "AnnImpl".hashCode();
    return hashCode;
  }
}
