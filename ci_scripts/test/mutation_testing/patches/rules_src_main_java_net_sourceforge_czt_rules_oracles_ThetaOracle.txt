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
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.Factory;

public class ThetaOracle
  extends AbstractOracle
{
  boolean decorated_;

  public ThetaOracle(boolean decorated)
  {
    decorated_ = decorated;
  }

  public Set<Binding> check(List<? extends Term> args, SectionManager manager, String section)
    throws UnboundJokerException
  {
    Factory factory = new Factory(new ProverFactory());
    Expr expr = (Expr) ProverUtils.removeJoker((Term) args.get(0));
    Stroke stroke = null;
    Expr result;
    if (decorated_) {
      stroke = (Stroke)  ProverUtils.removeJoker((Term) args.get(1));
      result = (Expr) args.get(2);
    }
    else {
      result = (Expr) args.get(1);
    }
    List<? extends ErrorAnn> errors =
      TypeCheckUtils.typecheck(expr, manager, false, false, true, section);
    if (errors == null || errors.isEmpty()) {
      TypeAnn typeAnn = (TypeAnn) expr.getAnn(TypeAnn.class);
      assert typeAnn != null;
      Type type = typeAnn.getType();
      if (type instanceof PowerType) {
        type = ((PowerType) type).getType();
        if (type instanceof SchemaType) {
          Signature sig = ((SchemaType) type).getSignature();
          ZDeclList zDeclList = factory.createZDeclList();
          for (NameTypePair nameType : sig.getNameTypePair()) {
            ZName origName = (ZName) nameType.getName();
            ZName name1 = factory.createZName(origName.getWord(),
                                              origName.getStrokeList());
            ZStrokeList strokes = factory.createZStrokeList();
            strokes.addAll(origName.getZStrokeList());
            if (stroke != null) strokes.add(stroke);
            ZName name2 = factory.createZName(origName.getWord(), strokes);
            RefExpr refExpr = factory.createRefExpr(name2);
            zDeclList.add(factory.createConstDecl(name1, refExpr));
          }
          BindExpr bindExpr = factory.createBindExpr(zDeclList);
          return UnificationUtils.unify(bindExpr, result);
        }
      }
    }
    return null;
  }
}
