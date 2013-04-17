/*
  Copyright (C) 2004, 2006 Petra Malik
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

package net.sourceforge.czt.print.ast;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.Expr2Impl;

public class Application
  extends Expr2Impl
{
  protected Application(PrintFactory factory)
  {
    super(factory);
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof ApplicationVisitor)
    {
      return ((ApplicationVisitor<R>) visitor).visitApplication(this);
    }
    return super.accept(visitor);
  }

  public Object[] getChildren()
  {
    Object[] result = { getLeftExpr(), getRightExpr() };
    return result;
  }

  public Application create(Object[] children)
  {
    Application result = new Application((PrintFactory) getFactory());
    result.setLeftExpr((Expr) children[0]);
    result.setRightExpr((Expr) children[1]);
    return result;
  }
}

