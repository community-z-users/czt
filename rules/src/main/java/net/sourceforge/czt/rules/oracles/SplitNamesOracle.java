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
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

public class SplitNamesOracle
  extends AbstractOracle
{
  private Factory factory_ = new Factory(new ProverFactory());

  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    final ZDeclList d = (ZDeclList)
      ProverUtils.removeJoker((Term) args.get(0));
    final DeclList d1 = (DeclList) args.get(1);
    final DeclList d2 = (DeclList) args.get(2);
    final DeclList d3 = (DeclList) args.get(3);
    final DeclList d4 = (DeclList) args.get(4);
    final ZDeclList r1 = factory_.createZDeclList();
    final ZDeclList r2 = factory_.createZDeclList();
    final ZDeclList r3 = factory_.createZDeclList();
    final ZDeclList r4 = factory_.createZDeclList();

    for (Decl decl : d) {
      if (! (decl instanceof VarDecl)) return null;
      VarDecl varDecl = (VarDecl) decl;
      assert varDecl.getName().size() == 1;
      ZName zName = (ZName) varDecl.getName().get(0);
      ZStrokeList strokes = zName.getZStrokeList();
      if (strokes.size() > 0) {
        Stroke last = strokes.get(strokes.size() - 1);
        if (last instanceof InStroke) {
          r1.add(undecorate(zName, varDecl));
        }
        else if (last instanceof NextStroke) {
          r3.add(undecorate(zName, varDecl));
        }
        else if (last instanceof OutStroke) {
          r4.add(undecorate(zName, varDecl));
        }
        else {
          r2.add(varDecl);
        }
      }
      else {
        r2.add(varDecl);
      }
    }
    Set<Binding> bindings1 = UnificationUtils.unify(r1, d1);
    Set<Binding> bindings2 = UnificationUtils.unify(r2, d2);
    Set<Binding> bindings3 = UnificationUtils.unify(r3, d3);
    Set<Binding> bindings4 = UnificationUtils.unify(r4, d4);
    if (bindings1 != null && bindings2 != null &&
        bindings2 != null && bindings4 != null) {
      Set<Binding> result = bindings1;
      result.addAll(bindings2);
      result.addAll(bindings3);
      result.addAll(bindings4);
      return result;
    }
    else {
      ProverUtils.reset(bindings1);
      ProverUtils.reset(bindings2);
      ProverUtils.reset(bindings3);
      ProverUtils.reset(bindings4);
    }
    return null;
  }

  private VarDecl undecorate(ZName zName, VarDecl varDecl)
  {
    ZStrokeList newStrokes = factory_.createZStrokeList();
    newStrokes.addAll(zName.getZStrokeList());
    newStrokes.remove(newStrokes.size() - 1);
    ZName newName =
      factory_.createZName(zName.getWord(), newStrokes, zName.getId());
    ZNameList newNameList = factory_.createZNameList();
    newNameList.add(newName);
    return factory_.createVarDecl(newNameList, varDecl.getExpr());
  }
}
