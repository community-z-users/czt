/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ExprImpl;
import net.sourceforge.czt.z.util.OperatorName;

/**
 * A function or generic operator application.
 *
 * @author Petra Malik
 */
public class OperatorApplication
  extends ExprImpl
{
  private OperatorName opName_;
  private ListTerm<Expr> args_ = new ListTermImpl<Expr>();
  private Precedence prec_;
  private Assoc assoc_;

  protected OperatorApplication(PrintFactory factory,
                                OperatorName opName,
                                List<Expr> args,
                                Precedence prec,
                                Assoc assoc)
  {
    super(factory);
    opName_ = opName;
    args_.addAll(args);
    prec_ = prec;
    assoc_ = assoc;
  }

  public OperatorName getOperatorName()
  {
    return opName_;
  }

  public List<Expr> getArgs()
  {
    return args_;
  }

  public Precedence getPrecedence()
  {
    return prec_;
  }

  public Assoc getAssoc()
  {
    return assoc_;
  }

  public <R> R accept(Visitor<R> visitor)
  {
    if (visitor instanceof OperatorApplicationVisitor) {
      OperatorApplicationVisitor<R> v =
        (OperatorApplicationVisitor<R>) visitor;
      return v.visitOperatorApplication(this);
    }
    return super.accept(visitor);
  }

  public Object[] getChildren()
  {
    return args_.toArray();
  }

  public OperatorApplication create(Object[] children)
  {
    List<Expr> argList = new ArrayList<Expr>(children.length);
    for (int i = 0; i < children.length; i++) {
      argList.add((Expr) children[0]);
    }
    return new OperatorApplication((PrintFactory) getFactory(),
                                   opName_, argList, prec_, assoc_);
  }
}
