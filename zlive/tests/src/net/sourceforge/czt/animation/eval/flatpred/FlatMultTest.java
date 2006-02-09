/**
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

package net.sourceforge.czt.animation.eval.flatpred;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.modeljunit.ModelTestCase;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZRefName;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class FlatMultTest
  extends ZTestCase
{
  private Expr i200 = factory_.createNumExpr(200);
  
  private FlatPred pred = new FlatMult(x,y,z);

  public void testMBT()
  throws FileNotFoundException
  {
    int interval = 2;
    FlatPredModel iut = new FlatPredModel(pred, new ZRefName[] {x,y,z},
                            "OII,IOI,IIO,III",
                            new Eval(1, "???", i3, i4, i12),
                            new Eval(0, "I?I", i2, i5, i11) // 11 is prime
                            );
    ModelTestCase model = new ModelTestCase(iut);
    CoverageHistory actions = new CoverageHistory(new ActionCoverage(), interval);
    CoverageHistory states = new CoverageHistory(new StateCoverage(), interval);
    CoverageHistory trans = new CoverageHistory(new TransitionCoverage(), interval);
    CoverageHistory tpair = new CoverageHistory(new TransitionPairCoverage(), interval);
    model.addCoverageMetric(actions);
    model.addCoverageMetric(states);
    model.addCoverageMetric(trans);
    model.addCoverageMetric(tpair);
    model.randomWalk(1500);

    // We print a vertical table of coverage statistics.
    // First we build the graph, so we get more accurate stats
    // (this also adds some transitions to the end of the history).
    model.buildGraph();
    int minlen = Integer.MAX_VALUE;
    List<List<Integer>> table = new ArrayList<List<Integer>>();
    System.out.print("Transitions");
    for (CoverageMetric cm : model.getCoverageMetrics()) {
      if (cm instanceof CoverageHistory) {
        System.out.print(","+cm.getName());
        List<Integer> history = ((CoverageHistory)cm).getHistory();
        table.add(history);
        if (history.size() < minlen)
          minlen = history.size();
      }
    }
    System.out.println();
    for (int i=0; i < minlen; i++) {
      System.out.print(i*interval);
      for (List<Integer> hist : table)
        System.out.print(","+hist.get(i));
      System.out.println();
    }
    model.printGraphDot("FlatMult.dot");
  }

  public static void main(String[] args)
  throws FileNotFoundException
  {
    new FlatMultTest().testMBT();
  }

  public void testEmpty()
  {
    Assert.assertNull("should not return a mode", pred.chooseMode(empty));
  }

  public void testIOO()
  {
    Envir envX = empty.add(x,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envX));
  }

  public void testOIO()
  {
    Envir envY = empty.add(y,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envY));
  }

  public void testOOI()
  {
    Envir envZ = empty.add(z,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envZ));
  }

  public void testIII()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i20);
    Envir envXYZ = envXY.add(z,i200);
    Mode m = pred.chooseMode(envXYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertEquals(0.5, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  10*20=200
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i200, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which fails:  10*20=10
    pred.getMode().getEnvir().setValue(z, i10);  // updates the environment
    pred.startEvaluation();
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIIO()
  {
    Envir envX = empty.add(x,i10);
    Envir envXY = envX.add(y,i20);
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(false, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(z));
    Assert.assertEquals(1.0, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i200, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIOI()
  {
    Envir envX = empty.add(x,i10);
    Envir envXZ = envX.add(z,i200);
    Mode m = pred.chooseMode(envXZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(false, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(y));
    Assert.assertEquals(1.0, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(y));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testOII()
  {
    Envir envY = empty.add(y,i20);
    Envir envYZ = envY.add(z,i200);
    Mode m = pred.chooseMode(envYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(false, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(x));
    Assert.assertEquals(1.0, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start a evaluation which succeeds:  10*20=200
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  20+10=30
    pred.getMode().getEnvir().setValue(z, i200);  // updates the environment
    pred.getMode().getEnvir().setValue(y, i10);  // updates the environment
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
  }
}




