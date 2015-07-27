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
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.unification.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

public class HideOracle
  extends AbstractOracle
{
  private Factory factory_ = new Factory(new ProverFactory());

  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    final ZDeclList d1 = (ZDeclList)
      ProverUtils.removeJoker((Term) args.get(0));
    final ZNameList nameList =
      (ZNameList) ProverUtils.removeJoker((Term) args.get(1));
    final DeclList d2 = (DeclList) args.get(2);

    ZDeclList result = factory_.createZDeclList();
    for (Name name : nameList) {
      String string = name.accept(new PrintVisitor());
      for (Decl decl : d1) {
	if (decl instanceof VarDecl) {
	  VarDecl varDecl = (VarDecl) decl;
	  Name n = varDecl.getName().get(0);
	  if (string.equals(n.accept(new PrintVisitor()))) {
	    result.add(decl);
	  }
	}
      }
    }
    return UnificationUtils.unify(result, d2);
  }
}
