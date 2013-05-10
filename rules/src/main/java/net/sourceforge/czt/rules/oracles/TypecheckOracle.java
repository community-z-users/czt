/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.rules.oracles;

import java.util.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.typecheck.z.util.CarrierSet;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

public class TypecheckOracle
  extends AbstractOracle
{
  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    Expr expr = (Expr) args.get(0);
    expr = (Expr) ProverUtils.removeJoker(expr);
    //    expr.getAnns().clear();
    final Expr type = (Expr) args.get(1);
    List<? extends ErrorAnn> errors =
      TypeCheckUtils.typecheck(expr, manager, false, false, true, section);
    if (errors == null || errors.isEmpty()) {
      TypeAnn typeAnn = (TypeAnn) expr.getAnn(TypeAnn.class);
      CarrierSet visitor = new CarrierSet();
      Term expr2 = (Term) typeAnn.getType().accept(visitor);
      expr2 = expr2.accept(new CopyVisitor(new Factory()));
      Set<Binding> result = UnificationUtils.unify(type, expr2);
      return result;
    }
    return null;
  }
}
