/*
  Copyright (C) 2005 Petra Malik
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

import java.util.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.typecheck.z.util.CarrierSet;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.TypeProvisoImpl;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * <p>A TypeProviso used by the prover.</p>
 *
 * @author Petra Malik
 */
public class ProverTypeProviso
  extends TypeProvisoImpl
  implements ProverProviso
{
  private Status status_ = Status.UNCHECKED;
  private Set<Binding> bindings_;

  public Set<Binding> getBindings()
  {
    return bindings_;
  }

  private void unify(Term term1, Term term2)
  {
    bindings_ = UnificationUtils.unify(term1, term2);
    if (bindings_ != null) {
      status_ = Status.PASS;
    }
    else {
      status_ = Status.FAIL;
    }
  }

  public void check(SectionManager manager, String section)
  {
    final Expr expr = (Expr) ProverUtils.removeJoker(getExpr());
    final Expr type = getType();
    List errors = TypeCheckUtils.typecheck(expr, manager, false, true, section);
    if (errors == null || errors.isEmpty()) {
      TypeAnn typeAnn = (TypeAnn) expr.getAnn(TypeAnn.class);
      CarrierSet visitor = new CarrierSet();
      Term expr2 = (Term) typeAnn.getType().accept(visitor);
      expr2 = expr2.accept(new CopyVisitor(new Factory()));
      unify(type, expr2);
    }
    else {
      System.err.println("Typeckecking failed:");
      System.err.println(errors);
      status_ = Status.FAIL;
    }
  }

  public Status getStatus()
  {
    return status_;
  }
}
