/*
  Copyright (C) 2005 Mark Utting
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

package net.sourceforge.czt.rules.ast;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DeclList;
import net.sourceforge.czt.z.impl.DeclListImpl;
import net.sourceforge.czt.zpatt.ast.Binding;

/**
 * A decl cons pair.
 *
 * @author Petra Malik
 */
public class DeclConsPairImpl
  extends DeclListImpl
  implements DeclConsPair
{
  private Decl car_;
  private DeclList cdr_;

  public DeclConsPairImpl(Decl car, DeclList cdr)
  {
    car_ = car;
    cdr_ = cdr;
  }

  public Decl car()
  {
    return car_;
  }

  public DeclList cdr()
  {
    return cdr_;
  }

  public void setCdr(DeclList cdr)
  {
    cdr_ = cdr;
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof DeclConsPairVisitor) {
      DeclConsPairVisitor<R> dcpv = (DeclConsPairVisitor<R>) visitor;
      return dcpv.visitDeclConsPair(this);
    }
    else {
      return super.accept(visitor);
    }
  }

  public Term create(Object[] args)
  {
    return new DeclConsPairImpl((Decl) args[0], (DeclList) args[1]);
  }

  public Object[] getChildren()
  {
    return new Object[] { car_, cdr_ };
  }

  public String toString()
  {
    return "[ " + car_ + " | " + cdr_ + "]";
  }
}
