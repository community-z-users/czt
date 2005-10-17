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

import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.unification.Unifier;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.session.*;
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
  private Status status_ = Status.UNCHECKED;

  public void check(SectionManager manager, String section)
  {
    try {
      Key key = new Key(section, DefinitionTable.class);
      DefinitionTable table = (DefinitionTable) manager.get(key);
      if (table != null) {
        RefExpr ref = (RefExpr) getLeftExpr();
        RefName refName = ref.getRefName();
        String word = refName.accept(new GetRefNameWordVisitor());
        DefinitionTable.Definition def = table.lookup(word);
        if (def != null) {
          Expr expr =
            (Expr) SimpleProver.copy(def.getExpr(),
                                     new Factory(new ProverFactory()));
          Set<Binding> bindings = new HashSet<Binding>();
          Unifier unifier = new Unifier(bindings);
          if (unifier.unify(expr, getRightExpr())) {
            status_ = Status.PASS;
          }
          else {
            status_ = Status.FAIL;
          }
        }
        else status_ = Status.UNKNOWN;
      }
    }
    catch (CommandException e) {
      status_ = Status.UNKNOWN;
      System.err.println(e);
    }
    return;
  }

  public Status getStatus()
  {
    return status_;
  }
}
