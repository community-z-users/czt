/**
Copyright (C) 2004 Mark Utting
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

package net.sourceforge.czt.animation.eval.flatpred;

import java.util.logging.Level;

import net.sourceforge.czt.animation.eval.Flatten;
import net.sourceforge.czt.animation.eval.ZFormatter;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.MuExpr;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.ast.ZSchText;


/**
 * A (JUnit) test class for testing the FlatSetComp class.
 *
 * @author Mark Utting
 */
public class FlatMuTest
  extends ZTestCase
{
  public void testMu1()
  {
    MuExpr mu = (MuExpr) parseExpr("(\\mu a:x \\upto y @ a*a)");

    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(mu.getZSchText());
    ZRefName resultName = sch.addExpr(mu.getExpr());
    FlatMu pred = new FlatMu(sch, resultName);
    
    FlatPredModel iut =
      new FlatPredModel(pred,
        new ZRefName[] {x,y,resultName},
        "IIO,III", // these are the only modes that should work
        new Eval(1, "II?", i2, i2, i4),
        new Eval(-1, "II?", i2, i1, i4)   // should throw undef
    );
    fsmRandomWalk(iut, 200);
  }

  public void testMu2()
  {
    MuExpr mu = (MuExpr) parseExpr("(\\mu a,b:x \\upto y @ a \\div 2)");

    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(mu.getZSchText());
    ZRefName resultName = sch.addExpr(mu.getExpr());
    FlatMu pred = new FlatMu(sch, resultName);
    
    FlatPredModel iut =
      new FlatPredModel(pred,
        new ZRefName[] {x,y,resultName},
        "IIO,III", // these are the only modes that should work
        new Eval(1, "II?", i2, i3, i1),   // ok, because 2/2 = 3/2.
        new Eval(-1, "IIO", i2, i4, i1)   // should throw undef
    );
    fsmRandomWalk(iut, 200);
  }

  public void testMuImplicit()
  {
    ZFormatter.startLogging("zlive.log", Level.FINEST);

    MuExpr mu = (MuExpr) parseExpr("(\\mu a,b:\\{1,3,5\\} |a<b<y)");
    Expr pair = parseExpr("(1,3)");

    FlatPredList sch = new FlatPredList(zlive_);
    Flatten flatten = new Flatten(zlive_);
    ZSchText stext = mu.getZSchText();
    sch.addSchText(stext);
    Expr expr = mu.getExpr();
    if (expr == null)
      expr = flatten.charTuple(stext.getZDeclList());
    ZRefName resultName = sch.addExpr(expr);
    FlatMu pred = new FlatMu(sch, resultName);
    
    FlatPredModel iut =
      new FlatPredModel(pred,
        new ZRefName[] {y,resultName},
        "IIO,III,IOI", // these are the modes that should work (IOI=II)
        new Eval(1, "I?", i5, pair),
        new Eval(-1, "IO", i20, pair)  // should throw undef
    );
    fsmRandomWalk(iut, 200);
    ZFormatter.stopLogging();
  }
}




