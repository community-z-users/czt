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

package net.sourceforge.czt.zpatt.util;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.JokerExprImpl;

public class ProverJokerExpr
  extends JokerExprImpl
  implements Joker
{
  private JokerExprBinding binding_;

  protected ProverJokerExpr(String name)
  {
    super.setName(name);
    binding_ = new JokerExprBindingImpl(this);
  }

  public Term boundTo()
  {
    return getBinding().getExpr();
  }

  public Binding bind(Term term)
  {
    if (! (term instanceof Expr)) {
      String message = "Cannot bind " + term + " to a a JokerExpr";
      throw new IllegalArgumentException(message);
    }
    getBinding().setExpr((Expr) term);
    return getBinding();
  }

  public JokerExprBinding getBinding()
  {
    return binding_;
  }

  public void setName(String name)
  {
    throw new UnsupportedOperationException();
  }

  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }
}
