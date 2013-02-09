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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.DefinitionType;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.ast.GetNameWordVisitor;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.ast.ProverJokerExpr;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

public class LookupOracle
  extends AbstractOracle
{
  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    Key<DefinitionTable> key = new Key<DefinitionTable>(section, DefinitionTable.class);
    DefinitionTable table;
    try {
      table = manager.get(key);
    }
    catch (CommandException e) {
      table = null;
    }
    if (table != null) {
      Factory factory = new Factory(new ProverFactory());
      CopyVisitor copyVisitor = new CopyVisitor(factory);
      RefExpr ref = (RefExpr) ProverUtils.removeJoker((Term) args.get(0));
      Expr rightExpr = (Expr) args.get(1);
      assert ref.getExprList() != null;
      String word = ref.getName().accept(new GetNameWordVisitor());
      DefinitionTable.Definition def = table.lookup(word);
      if (def != null &&
          def.getDefinitionType().equals(DefinitionType.CONSTDECL)) {
        assert def.getDeclNames() != null;
        List<Expr> formals = new ArrayList<Expr>();
        Map<ZName,Expr> formalMap = new HashMap<ZName,Expr>();
        jokerizeNames(def.getDeclNames(), formals, formalMap, copyVisitor);
        copyVisitor.setGeneralize(word, formalMap); // start generalizing
        Expr defrhs = (Expr) def.getExpr().accept(copyVisitor);
        copyVisitor.setGeneralize("", null);  // finish generalizing
        Set<Binding> bindings = UnificationUtils.unify(defrhs, rightExpr);
        ZExprList actuals = ref.getZExprList();
        if (bindings == null | formals.size() != actuals.size()) {
          return null;
        }
        else {
          for (int i=0; i < formals.size(); i++) {
            Expr joker = formals.get(i);
            Expr actual = actuals.get(i);
            Set<Binding> b = UnificationUtils.unify(joker, actual);
            if (b == null) {
              ProverUtils.reset(bindings);
              return null;
            }
            else {
              bindings.addAll(b);
            }
          }
        }
        /*
        // Now run the typechecker over the instantiated defn.
        // so that the whole term will be properly type annotated.
        List<? extends ErrorAnn> errors =
        TypeCheckUtils.typecheck(getRightExpr(), manager, false false, true, section);
        if (errors != null && ! errors.isEmpty()) {
        throw new TypeErrorException("typecheck failure after unfolding "+word, 
        errors);
        }
        */
        return bindings;
      }
    }
    return null;
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
}
