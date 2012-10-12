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
 * An implementation for NameTypePair that hides VariableType instances
 * if they have a value.
 */
public class NameTypePairImpl
  extends TermImpl
  implements NameTypePair
{
  protected NameTypePairImpl(NameTypePair nameTypePair)
  {
    super(nameTypePair);
  }

  public void setName(Name declName)
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    nameTypePair.setName(declName);
  }

  public Name getName()
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    return nameTypePair.getName();
  }

  public ZName getZName()
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    return nameTypePair.getZName();
  }

  public void setType(Type type)
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    nameTypePair.setType(type);
  }

  public Type getType()
  {
    NameTypePair nameTypePair = (NameTypePair) term_;
    Type result = nameTypePair.getType();
    if (result instanceof VariableType) {
      VariableType vType = (VariableType) result;
      if (vType.getValue() != null) {
        result = vType.getValue();
      }
    }
    return result;
  }

  public Object[] getChildren()
  {
    Object[] erg = { getName(), getType() };
    return erg;
  }

  public NameTypePairImpl create(Object [] args)
  {
    NameTypePair pair = (NameTypePair) term_.create(args);
    NameTypePairImpl result = new NameTypePairImpl(pair);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof NameTypePairVisitor) {
      NameTypePairVisitor<R> visitor = (NameTypePairVisitor<R>) v;
      return visitor.visitNameTypePair(this);
    }
    return super.accept(v);
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof NameTypePair) {
      NameTypePair pair = (NameTypePair) obj;
      if (getName() != null)
      {
        if (!getName().equals(pair.getName()))
        {
          return false;
        }
      }
      else
      {
        if (pair.getName() != null)
        {
          return false;
        }
      }
      if (getType() != null)
      {
        if (!getType().equals(pair.getType()))
        {
          return false;
        }
      }
      else
      {
        if (pair.getType() != null)
        {
          return false;
        }
      }
      return true;
    }
    return false;
  }

  public int hashCode()
  {
    final int constant = 31;

    int hashCode = super.hashCode();
    hashCode += "NameTypePairImpl".hashCode();
    if (getName() != null) {
      hashCode += constant * getName().hashCode();
    }
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}
