/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit;

import java.io.StringWriter;
import java.util.List;
import java.util.Random;

import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.modeljunit.examples.FSM;
import junit.framework.Assert;
import junit.framework.TestCase;

public class RandomTesterTest extends TestCase
{
  /** Checks that we always get a consistent sequence of random numbers. */
  public static void testRandom()
  {
    Random rand = new Random(Tester.FIXEDSEED);
    assertEquals(965, rand.nextInt(1000));
    assertEquals(600, rand.nextInt(1000));
    assertEquals(483, rand.nextInt(1000));
    assertEquals(344, rand.nextInt(1000));
  }

  /** This tests a random walk, plus ActionCoverage metric with history.*/
  public static void testRandomWalk()
  {
    RandomTester tester = new RandomTester(new FSM());
    //System.out.println("action0="+tester.getModel().getActionName(0));
    //System.out.println("action1="+tester.getModel().getActionName(1));
    //System.out.println("action2="+tester.getModel().getActionName(2));
    //System.out.println("action3="+tester.getModel().getActionName(3));
    CoverageHistory metric =
      new CoverageHistory(new ActionCoverage(), 1);
    tester.addListener(metric);
    tester.setRandom(new Random(3));
    tester.generate(5);
    int coverage = metric.getCoverage();
    Assert.assertEquals(1, coverage);
    Assert.assertEquals(4, metric.getMaximum());
    List<Integer> hist = metric.getHistory();
    Assert.assertNotNull(hist);
    Assert.assertEquals("Incorrect history size.", 6, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
    Assert.assertEquals(new Integer(coverage), hist.get(hist.size() - 1));

    // we print this just for interest
    //    System.out.println("Action coverage: " + metric.getPercentage());
    //    System.out.print("History: ");
    //    for (Integer cov : metric.getHistory())
    //      System.out.print(cov + ", ");
    //    System.out.println();

    metric.clear();
    hist = metric.getHistory();
    Assert.assertNotNull(hist);
    Assert.assertEquals("History not reset.", 1, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
  }

  /** A helper method for testing coverage metrics, using the FSM class.
   *  It checks that the coverage is 0/-1 initially,
   *  then 0/max1 after buildGraph and reset,
   *  then cov1/max after tr1 random walk transitions,
   *  then cov2/max after tr2 random walk transitions,
   *  ...  covN/max after trN random walk transitions.
   *  (each random walk starts from the initial state
   *  with the same random seed, so will follow the same path).
   *
   *  @param metric  The CoverageMetric to test.
   *  @param max     The value of metric.getMaximum() after buildGraph.
   *  @param expect  An array of {tr1,cov1, tr2,cov2, ..., trN,covN}
   */
  public void FsmCoverage(CoverageMetric metric, int max, int... expect)
  {
    RandomTester tester = new RandomTester(new FSM());
    tester.addListener(metric);
    //    System.out.println("Testing "+metric.getName());
    Assert.assertEquals(0, metric.getCoverage());
    if (metric.getMaximum() != -1) {
      Assert.assertEquals(max, metric.getMaximum()); // should be correct or -1
    }
    // Build the graph
    tester.buildGraph();

    Assert.assertTrue(metric.getCoverage() > 0);
    Assert.assertEquals(max, metric.getMaximum());
    metric.clear();
    Assert.assertEquals(0, metric.getCoverage());
    Assert.assertEquals(max, metric.getMaximum());
    Assert.assertEquals(0.0F, metric.getPercentage(), 0.1F);

    tester.getModel().doReset("Initial");
    for (int i = 0; i < expect.length-1; i += 2) {
      int cov = expect[i+1];
      // System.out.println("After random walk of length "+expect[i]+
      //           " we expect "+metric.getName()+" = "+cov);
      tester.setRandom(new Random(tester.FIXEDSEED));
      tester.reset();
      tester.generate(expect[i]);
      Assert.assertEquals(cov, metric.getCoverage());
      Assert.assertEquals(max, metric.getMaximum());
      Assert.assertEquals((100.0F * cov)/max, metric.getPercentage(), 0.1F);
    }
  }

  /** This test is a bit dependent on the path of the random walk.
   *  It may need adjusting when the seed or random walk algorithm changes.
   */
  public void testActionCoverage()
  {
    //    System.out.println("Starting testActionCoverage");
    FsmCoverage(new ActionCoverage(), 4,
        new int[] {1,1, 3,3, 20,4});
  }

  /** This test is a bit dependent on the path of the random walk.
   *  It may need adjusting when the seed or random walk algorithm changes.
   */
  public void testStateCoverage()
  {
    //    System.out.println("Starting testStateCoverage");
    FsmCoverage(new StateCoverage(), 3,
        new int[] {1,1, 2,2, 3,3, 20,3});
  }

  /** This test is a bit dependent on the path of the random walk.
   *  It may need adjusting when the seed or random walk algorithm changes.
   */
  public void testTransitionCoverage()
  {
    //    System.out.println("Starting testTransitionCoverage");
    FsmCoverage(new TransitionCoverage(), 5,
        new int[] {1,1, 3,3, 40,5});
  }

  /** This test is a bit dependent on the path of the random walk.
   *  It may need adjusting when the seed or random walk algorithm changes.
   */
  public void testTransitionPairCoverage()
  {
    //    System.out.println("Starting testTransitionPairCoverage");
    FsmCoverage(new TransitionPairCoverage(), 10,
        new int[] {1,0, 2,1, 3,2, 200,9});
  }
  
  public void testPrintCoverage()
  {
    RandomTester tester = new RandomTester(new FSM());
    tester.addListener("transition coverage");
    tester.addCoverageMetric(new ActionCoverage());
    tester.buildGraph();
    tester.generate(100);
    StringWriter out = new StringWriter();
    tester.getModel().setOutput(out);
    tester.printCoverage();
    assertEquals("action coverage: 4/4\n"
        + "transition coverage: 5/5\n",
        out.toString());
  }
}
