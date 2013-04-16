/*
  Copyright (C) 2007 Mark Utting
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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
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

public class SchemaMinusOracle
  extends AbstractOracle
{
  /**
   * Implements the [D1|true] schemaminus [D2|true] oracle.
   * This calculates the signature D1 minus D2.
   */
  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    Factory factory = new Factory(new ProverFactory());
    ZDeclList decls1 = (ZDeclList)
      ProverUtils.removeJoker((Term) args.get(0));
    ZDeclList decls2 = (ZDeclList)
      ProverUtils.removeJoker((Term) args.get(1));
    // create a map of the names in decls2.
    Map<String,Expr> map2 = new HashMap<String,Expr>();
    for (Decl decl : decls2) {
      if (! (decl instanceof VarDecl)) return null;
      VarDecl vdecl = (VarDecl) decl;
      String name = vdecl.getName().get(0).accept(new PrintVisitor());
      map2.put(name,vdecl.getExpr());
    }
    // now go through decls1, and filter out any names in map2
    ZDeclList result = factory.createZDeclList();
    for (Decl decl : decls1) {
      if (! (decl instanceof VarDecl)) return null;
      VarDecl vdecl = (VarDecl) decl;
      String name = vdecl.getName().get(0).accept(new PrintVisitor());
      if (map2.containsKey(name)) {
        assert map2.get(name).equals(vdecl.getExpr());
      }
      else {
        result.add(decl);
      }
    }
    //ZSchText schtext =
    //  factory.createZSchText(result, factory.createTruePred());
    //SchExpr schExpr = factory.createSchExpr(schtext);
    return UnificationUtils.unify(result, (DeclList) args.get(2));
  }
}
