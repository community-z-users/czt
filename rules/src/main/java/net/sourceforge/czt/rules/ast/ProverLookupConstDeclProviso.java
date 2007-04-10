/*
  Copyright (C) 2005, 2006 Mark Utting, Petra Malik
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.ast.ProverJokerExpr;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.LookupConstDeclProvisoImpl;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * <p>A LookupConstDeclProviso used by the prover.</p>
 *
 * @author Petra Malik
 */
public class ProverLookupConstDeclProviso
  extends LookupConstDeclProvisoImpl
  implements ProverProviso
{
  private Logger LOG = Logger.getLogger("net.sourceforge.czt.rules");
  private Status status_ = Status.UNCHECKED;
  private Set<Binding> bindings_;

  public Set<Binding> getBindings()
  {
    return bindings_;
  }

  /** This dereferences the expression.
   *  That is, skips over any bound jokers.
   */
  public Expr deref(Expr expr)
  {
    if (expr instanceof ProverJokerExpr) {
      ProverJokerExpr joker = (ProverJokerExpr) expr;
      Expr result = (Expr) joker.boundTo();
      if (result != null)
        return deref(result);
    }
    return expr;
  }

  public void check(SectionManager manager, String section)
  {
    LOG.entering("ProverLookupConstDeclProviso", "check");
    Expr deflhs = deref(getLeftExpr());
    if ( ! (deflhs instanceof RefExpr)) {
      status_ = Status.FAIL;
    }
    else {
      try {
        CopyVisitor copyVisitor = new CopyVisitor(new Factory(new ProverFactory()));
        Key key = new Key(section, DefinitionTable.class);
        DefinitionTable table = (DefinitionTable) manager.get(key);
        if (table != null) {
          RefExpr ref = (RefExpr) deflhs;
          assert ref.getExprList() != null;
          String word = ref.getName().accept(new GetNameWordVisitor());
          DefinitionTable.Definition def = table.lookup(word);
          LOG.fine("found def="+def);
          if (def != null) {
            status_ = Status.PASS;  // by default
            assert def.getDeclNames() != null;
            List<Expr> formals = new ArrayList<Expr>();
            Map<ZName,Expr> formalMap = new HashMap<ZName,Expr>();
            jokerizeNames(def.getDeclNames(), formals, formalMap, copyVisitor);
            copyVisitor.setGeneralize(word, formalMap); // start generalizing
            Expr defrhs = (Expr) def.getExpr().accept(copyVisitor);
            copyVisitor.setGeneralize("", null);  // finish generalizing
            unify(defrhs, getRightExpr());
            ZExprList actuals = ref.getZExprList();
            if (formals.size() != actuals.size()) {
              status_ = Status.FAIL;
            }
            else {
              for (int i=0; i < formals.size(); i++) {
                Expr joker = formals.get(i);
                Expr actual = actuals.get(i);
                LOG.finer("unifying type param "+i+": "+joker+" =? "+actual);
                unify(joker, actual);
              }
            }
            /*
            // Now run the typechecker over the instantiated defn.
            // so that the whole term will be properly type annotated.
            List<? extends ErrorAnn> errors =
              TypeCheckUtils.typecheck(getRightExpr(), manager, false, true, section);
            if (errors != null && ! errors.isEmpty()) {
              status_ = Status.FAIL;
              throw new TypeErrorException("typecheck failure after unfolding "+word, 
                  errors);
            }
            */
          }
          else status_ = Status.UNKNOWN;
        }
      }
      catch (CommandException e) {
        status_ = Status.UNKNOWN;
        System.err.println(e);
      }
    }
    LOG.exiting("ProverLookupConstDeclProviso", "check", status_);
  }

  
  /** Transforms formal type parameters into expression jokers. */
  public void jokerizeNames(ZNameList names, List<Expr> jokers,
      Map<ZName,Expr> jokerMap, CopyVisitor copy)
  {
    for (Name n : names) {
      if ( ! (n instanceof ZName))
        throw new RuntimeException("Illegal defn type parameter: "+n);
      ZName name = (ZName) n;
      Expr joker = copy.freshJokerExpr(name.getWord());
      assert joker instanceof ProverJokerExpr;
      jokers.add(joker);
      jokerMap.put(name, joker);
    }
  }

  private void unify(Term term1, Term term2)
  {
    try {
      bindings_ = UnificationUtils.unify(term1, term2);
      if (bindings_ == null) {
        LOG.finer("FAILED to unify: "+term1+" and "+term2);
        status_ = Status.FAIL;
      }
    }
    catch(Exception e) { // UnificationException e)
      String message = "Failed to unify " + term1 + " and " + term2;
      status_ = Status.FAIL;
      throw new RuntimeException(message, e);
    }
  }

  public Status getStatus()
  {
    return status_;
  }
}
