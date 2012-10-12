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
 * An implementation for NameSectTypeTriple that hides VariableType instances
 * if they have a value.
 */
public class NameSectTypeTripleImpl
  extends TermImpl
  implements NameSectTypeTriple
{
  protected NameSectTypeTripleImpl(NameSectTypeTriple triple)
  {
    super(triple);
  }

  public void setSect(String section)
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    triple.setSect(section);
  }

  public void setName(Name declName)
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    triple.setName(declName);
  }

  public void setType(Type type)
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    triple.setType(type);
  }

  public String getSect()
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    return triple.getSect();
  }

  public Name getName()
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    return triple.getName();
  }

  public ZName getZName()
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    return triple.getZName();
  }

  public Type getType()
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_;
    Type result = triple.getType();
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
    Object[] erg = { getName(), getSect(), getType() };
    return erg;
  }

  public NameSectTypeTripleImpl create(Object [] args)
  {
    NameSectTypeTriple triple = (NameSectTypeTriple) term_.create(args);
    NameSectTypeTripleImpl result = new NameSectTypeTripleImpl(triple);
    return result;
  }

  /**
   * Accepts a visitor.
   */
  public <R> R accept(net.sourceforge.czt.util.Visitor<R> v)
  {
    if (v instanceof NameSectTypeTripleVisitor) {
      NameSectTypeTripleVisitor<R> visitor = (NameSectTypeTripleVisitor<R>) v;
      return visitor.visitNameSectTypeTriple(this);
    }
    return super.accept(v);
  }

  public boolean equals(Object obj)
  {
    if (obj instanceof NameSectTypeTriple) {
      NameSectTypeTriple triple = (NameSectTypeTriple) obj;
      if (!getSect().equals(triple.getSect()) ||
          !getName().equals(triple.getName()) ||
          !getType().equals(triple.getType())) {
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
    hashCode += "NameSectTypeTripleImpl".hashCode();
    if (getName() != null) {
      hashCode += constant * getName().hashCode();
    }
    if (getSect() != null) {
      hashCode += constant * getSect().hashCode();
    }
    if (getType() != null) {
      hashCode += constant * getType().hashCode();
    }
    return hashCode;
  }
}
