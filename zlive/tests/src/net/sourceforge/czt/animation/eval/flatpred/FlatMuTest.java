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

import java.io.IOException;
import java.net.URL;
import java.util.*;
import java.math.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.animation.eval.*;
import net.sourceforge.czt.animation.eval.flatpred.*;


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
    MuExpr mu = (MuExpr) parseExpr("(\\mu a:x \\upto y @ x*x)" /* = z */);

    FlatPredList sch = new FlatPredList(zlive_);
    sch.addSchText(mu.getZSchText());
    // Now build an 'expr = result' predicate
    ZRefName resultName = zlive_.createNewName();
    RefExpr resultExpr = factory_.createRefExpr(resultName);
    Pred eq = factory_.createEquality(resultExpr, resultExpr);
    sch.addPred(eq);
    FlatMu pred = new FlatMu(sch, resultName);
    
    FlatPredModel iut = new FlatPredModel(pred, new ZRefName[] {x,y,z},
        new Eval(1, "II?", i2, i2, i4),
        new Eval(0, "II?", i2, i1, i4)   // no solutions
    );
    // TODO:  fsmRandomWalk(iut, 200);
  }
}




