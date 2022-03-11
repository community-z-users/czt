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

import java.util.List;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * Implements the 'decorated expression' oracle.  For example, given
 * [D] ', this will create a primed version of [D].
 */
public class DecorateOracle
  extends AbstractOracle
{
  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    Expr expr = (Expr) ProverUtils.removeJoker((Term) args.get(0));
    Stroke stroke = (Stroke) ProverUtils.removeJoker((Term) args.get(1));
    Expr result = (Expr) args.get(2);
    if (expr instanceof SchExpr) {
      SchExpr schExpr = (SchExpr) expr;
      // We typecheck before decorating to ensure that ids are correct
      List<? extends ErrorAnn> errors =
        TypeCheckUtils.typecheck(expr, manager, false, false, true, section);
      if (errors == null || errors.isEmpty()) {
        final CollectStateVariablesVisitor collectVisitor =
          new CollectStateVariablesVisitor();
        schExpr.getZSchText().getDeclList().accept(collectVisitor);
        final DecorateNamesVisitor visitor =
          new DecorateNamesVisitor(collectVisitor.getVariables(), stroke);
        schExpr = (SchExpr) schExpr.accept(visitor);
        if (schExpr != null) {
          return UnificationUtils.unify(schExpr, result);
        }
      }
    }
    return null;
  }


  /**
   * Assumes that the term is properly typechecked (i.e. the ids are
   * correct).  When decorating expressions and predicates, it
   * decorates only names that exactly match a member of
   * <code>declNames_</code> (including ids).  We hope that nested
   * schema expressions are therefore not a problem (we should prove
   * this).
   *
   * @czt.todo Detect references to schemas (those are not handled
   *           by this oracle).  Either throw an exception or add
   *           a renaming.
   */
  public static class DecorateNamesVisitor
    implements TermVisitor<Term>,
               ZNameVisitor<Term>
  {
    private Set<Name> declNames_;
    private Factory factory_ = new Factory(new ProverFactory());

    /**
     * The stroke to be added to names.
     */
    private Stroke stroke_;

    public DecorateNamesVisitor(Set<Name> declNames, Stroke stroke)
    {
      declNames_ = declNames;
      stroke_ = stroke;
    }

    public Term visitTerm(Term term)
    {
      return (Term) VisitorUtils.visitTerm(this, term, true);
    }

    public Term visitZName(ZName zName)
    {
      if (declNames_.contains(zName)) {
	ZStrokeList strokes = factory_.createZStrokeList();
	strokes.addAll(zName.getZStrokeList());
	strokes.add(stroke_);
        return factory_.createZName(zName.getWord(), strokes, zName.getId());
      }
      return zName;
    }
  }
}
