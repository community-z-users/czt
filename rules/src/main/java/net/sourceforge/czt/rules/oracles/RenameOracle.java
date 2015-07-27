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
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.Joker;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * Implements the rename oracle.
 */
public class RenameOracle
  extends AbstractOracle
{
  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    Expr expr = (Expr) ProverUtils.removeJoker((Term) args.get(0));
    ZRenameList renameList = (ZRenameList)
      ProverUtils.removeJoker((Term) args.get(1));
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
        final RenameVisitor visitor =
          new RenameVisitor(collectVisitor.getVariables(), renameList);
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
   */
  public static class RenameVisitor
    implements InclDeclVisitor<Term>,
               TermVisitor<Term>,
               ZNameVisitor<Term>
  {
    private Factory factory_ = new Factory(new ProverFactory());
    private ZRenameList renameList_;
    private Map<Name,Name> map_ = new HashMap<Name,Name>();

    public RenameVisitor(Set<Name> declNames, ZRenameList renameList)
    {
      renameList_ = renameList;
      Map<String,Name> names = new HashMap<String,Name>();
      for (Name name: declNames) {
	names.put(name.accept(new PrintVisitor()), name);
      }
      for (NewOldPair pair : renameList) {
	Name old =
	  names.get(pair.getName().get(1).accept(new PrintVisitor()));
	if (old != null) {
	  map_.put(old, (Name) pair.getName().get(0));
	}
      }
    }

    public Term visitInclDecl(InclDecl inclDecl)
    {
      // TODO: visit children?
      RenameExpr renameExpr =
        factory_.createRenameExpr(inclDecl.getExpr(), renameList_);
      InclDecl result = (InclDecl)
	inclDecl.create(new Object[] { renameExpr });
      return result;
    }

    public Term visitTerm(Term term)
    {
      if (term instanceof Joker) {
        Joker joker = (Joker) term;
        Term boundTo = joker.boundTo();
        if (boundTo != null) {
          return boundTo.accept(this);
        }
        throw new RuntimeException("Found unbound Joker");
      }
      return (Term) VisitorUtils.visitTerm(this, term, true);
    }

    public Term visitZName(ZName zName)
    {
      Name newName = map_.get(zName);
      if (newName != null) return newName;
      return zName;
    }
  }
}
