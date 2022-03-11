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
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import nz.ac.waikato.modeljunit.GreedyTester;
import nz.ac.waikato.modeljunit.ModelListener;
import nz.ac.waikato.modeljunit.Tester;
import nz.ac.waikato.modeljunit.coverage.ActionCoverage;
import nz.ac.waikato.modeljunit.coverage.CoverageHistory;
import nz.ac.waikato.modeljunit.coverage.StateCoverage;
import nz.ac.waikato.modeljunit.coverage.TransitionCoverage;
import nz.ac.waikato.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.ZName;


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
  private Bounds bounds_ = new Bounds(null);

  @Override
  public void setUp()
  {
    pred.inferBounds(bounds_);
  }

  public void testToString()
  {
    assertEquals("z = x * y", pred.toString());
  }

  public void testMBT()
  throws FileNotFoundException
  {
    int interval = 2;
    FlatPredModel iut = new FlatPredModel(pred, 
        new ZName[] {x,y,z},
          // OII and IOI modes are not allowed because x and y can be zero
          "IIO,III",
          new Eval(1, "???", i3, i4, i12),
          new Eval(0, "I?I", i2, i5, i11) // 11 is prime
      );
    Tester tester = new GreedyTester(iut);
    CoverageHistory actions = new CoverageHistory(new ActionCoverage(), interval);
    CoverageHistory states = new CoverageHistory(new StateCoverage(), interval);
    CoverageHistory trans = new CoverageHistory(new TransitionCoverage(), interval);
    CoverageHistory tpair = new CoverageHistory(new TransitionPairCoverage(), interval);
    tester.addCoverageMetric(actions);
    tester.addCoverageMetric(states);
    tester.addCoverageMetric(trans);
    tester.addCoverageMetric(tpair);
    tester.generate(1500);

    // We print a vertical table of coverage statistics.
    // First we build the graph, so we get more accurate stats
    // (this also adds some transitions to the end of the history).
    tester.buildGraph();
    int minlen = Integer.MAX_VALUE;
    List<List<Integer>> table = new ArrayList<List<Integer>>();
    //    System.out.print("Transitions");
    for (String name : tester.getModel().getListenerNames()) {
      ModelListener cm = tester.getModel().getListener(name);
      if (cm instanceof CoverageHistory) {
        //        System.out.print(","+cm.getName());
        List<Integer> history = ((CoverageHistory)cm).getHistory();
        table.add(history);
        if (history.size() < minlen)
          minlen = history.size();
      }
    }
    //    System.out.println();
    //    for (int i=0; i < minlen; i++) {
    //      System.out.print(i*interval);
    //      for (List<Integer> hist : table)
    //        System.out.print(","+hist.get(i));
    //      System.out.println();
    //    }
    //model.printGraphDot("FlatMult.dot");
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
    Envir envX = empty.plus(x,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envX));
  }

  public void testOIO()
  {
    Envir envY = empty.plus(y,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envY));
  }

  public void testOOI()
  {
    Envir envZ = empty.plus(z,i10);
    Assert.assertNull("should not return a mode", pred.chooseMode(envZ));
  }

  public void testIII()
  {
    Envir envX = empty.plus(x,i10);
    Envir envXY = envX.plus(y,i20);
    Envir envXYZ = envXY.plus(z,i200);
    Mode m = pred.chooseMode(envXYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, m.getSolutions(), ACCURACY);
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
    Envir envX = empty.plus(x,i10);
    Envir envXY = envX.plus(y,i20);
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(false, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(z));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i200, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  /** Same as testIIO, but with big integer values. */
  public void testIIOBigInteger()
  {
    Envir envX = empty.plus(x,factory_.createNumExpr(3000000));
    Envir envXY = envX.plus(y,factory_.createNumExpr(4000000));
    Mode m = pred.chooseMode(envXY);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(false, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(z));
    Assert.assertEquals(Mode.ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    NumExpr twelveTrillion = factory_.createNumExpr(factory_.createZNumeral(
        BigInteger.valueOf(12000000).multiply(BigInteger.valueOf(1000000))));
    Assert.assertEquals("result value", twelveTrillion, m.getEnvir().lookup(z));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testIOI()
  {
    Envir envX = empty.plus(x,i10);
    Envir envXZ = envX.plus(z,i200);
    bounds_.addLower(x, new BigInteger("2"));
    pred.inferBounds(bounds_);
    Mode m = pred.chooseMode(envXZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(true, m.isInput(0));
    Assert.assertEquals(false, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(y));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(y));
    Assert.assertFalse(pred.nextEvaluation());
  }

  public void testOII()
  {
    Envir envY = empty.plus(y,i20);
    Envir envYZ = envY.plus(z,i200);
    bounds_.addUpper(y, new BigInteger("-2"));
    pred.inferBounds(bounds_);
    Mode m = pred.chooseMode(envYZ);
    Assert.assertTrue(m != null);
    Assert.assertEquals(false, m.isInput(0));
    Assert.assertEquals(true, m.isInput(1));
    Assert.assertEquals(true, m.isInput(2));
    Assert.assertTrue(m.getEnvir().isDefined(x));
    Assert.assertEquals(Mode.MAYBE_ONE_SOLUTION, m.getSolutions(), ACCURACY);
    pred.setMode(m);
    // Start an evaluation which succeeds:  x*20=200
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i10, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
    // Start a evaluation which succeeds:  x*10=200
    pred.getMode().getEnvir().setValue(z, i200);  // updates the environment
    pred.getMode().getEnvir().setValue(y, i10);  // updates the environment
    pred.startEvaluation();
    Assert.assertTrue(pred.nextEvaluation());
    Assert.assertEquals("result value", i20, m.getEnvir().lookup(x));
    Assert.assertFalse(pred.nextEvaluation());
  }
}
