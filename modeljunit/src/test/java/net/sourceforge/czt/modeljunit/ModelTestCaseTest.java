/**
 Copyright (C) 2006 Mark Utting
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

import java.util.BitSet;
import java.util.Iterator;
import java.util.List;

import junit.framework.Assert;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionPairCoverage;
import net.sourceforge.czt.modeljunit.examples.FSM;

/**
 * Unit tests for ModelTestCase
 */
public class ModelTestCaseTest extends TestCase
{
  /**
   * Create the test case
   *
   * @param testName name of the test case
   */
  public ModelTestCaseTest(String testName)
  {
    super(testName);
  }

  /**
   * @return the suite of tests being tested
   */
  public static Test suite()
  {
    return new TestSuite(ModelTestCaseTest.class);
  }

  public static void testEnabled()
  {
    ModelTestCase model = new ModelTestCase(new FSM());
    model.doReset(true);
    Assert.assertEquals("0", model.getCurrentState());
    int action0 = model.fsmFindAction("action0");
    int action1 = model.fsmFindAction("action1");
    int action2 = model.fsmFindAction("action2");
    int actionNone = model.fsmFindAction("actionNone");
    int rubbish = model.fsmFindAction("rubbish");
    Assert.assertTrue(action0 >= 0);
    Assert.assertTrue(action1 >= 0);
    Assert.assertTrue(action2 >= 0);
    Assert.assertTrue(actionNone >= 0);
    Assert.assertEquals(-1, rubbish);
    Assert.assertEquals("action0", model.getActionName(action0));
    Assert.assertEquals("action1", model.getActionName(action1));
    Assert.assertEquals("action2", model.getActionName(action2));
    Assert.assertEquals("actionNone", model.getActionName(actionNone));

    // check enabled actions of state 0.
    BitSet enabled = model.currentEnabledActions();
    Assert.assertEquals(false, enabled.get(action0));
    Assert.assertEquals(false, enabled.get(action1));
    Assert.assertEquals(true, enabled.get(action2));
    Assert.assertEquals(true, enabled.get(actionNone));

    // Now take action2, to state 2, and check its enabled actions.
    model.doAction(action2);
    Assert.assertEquals("2", model.getCurrentState().toString());
    enabled = model.currentEnabledActions();
    Assert.assertEquals(true, enabled.get(action0));
    Assert.assertEquals(true, enabled.get(action1));
    Assert.assertEquals(false, enabled.get(action2));
    Assert.assertEquals(true, enabled.get(actionNone));
  }

  /** This tests a random walk, plus ActionCoverage metric with history.*/
  public static void testRandomWalk()
  {
    ModelTestCase model = new ModelTestCase(new FSM());
    CoverageHistory metric = new CoverageHistory(new ActionCoverage(), 1);
    model.addCoverageMetric(metric);
    model.randomWalk(4); // 4 transitions plus a few resets
    int coverage = metric.getCoverage();
    Assert.assertEquals(3, coverage);
    Assert.assertEquals(-1, metric.getMaximum()); // unknown.
    List<Integer> hist = metric.getHistory();
    Assert.assertNotNull(hist);
    Assert.assertEquals("Incorrect history size.", 7, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
    Assert.assertEquals(new Integer(coverage), hist.get(hist.size() - 1));

    // we print this just for interest
    //    System.out.println("Action coverage: " + metric.getPercentage());
    //    System.out.print("History: ");
    //    for (Integer cov : metric.getHistory())
    //      System.out.print(cov + ", ");
    //    System.out.println();

    model.resetCoverageMetrics();
    hist = metric.getHistory();
    Assert.assertNotNull(hist);
    Assert.assertEquals("History not reset.", 1, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
  }

  /** This tests a greedy random walk, plus TransitionCoverage metric with history */
  public static void testGreedyRandomWalk()
  {
    ModelTestCase model = new ModelTestCase(new FSM());
    CoverageHistory metric = new CoverageHistory(new TransitionCoverage(), 1);
    model.addCoverageMetric(metric);
    model.greedyRandomWalk(7); // 7 transitions plus a few resets
    int coverage = metric.getCoverage();
    Assert.assertEquals(5, coverage);
    Assert.assertEquals(-1, metric.getMaximum());
    List<Integer> hist = metric.getHistory();
    Assert.assertNotNull(hist);
    Assert.assertEquals("Incorrect history size.", 10, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
    Assert.assertEquals(new Integer(coverage), hist.get(hist.size() - 1));
  }

  public static void testBuildGraph()
  {
    ModelTestCase model = new ModelTestCase(new FSM());
    model.buildGraph();
    InspectableGraph graph = model.getGraph();
    // now check that the correct graph has been built.
    Assert.assertEquals(3, graph.numVertices());
    Assert.assertEquals(5, graph.numEdges());
    Vertex s0 = model.getVertex("0");
    Vertex s1 = model.getVertex("1");
    Vertex s2 = model.getVertex("2");
    Assert.assertNotNull(s0);
    Assert.assertNotNull(s1);
    Assert.assertNotNull(s2);
    Assert.assertEquals("0", s0.element());
    Assert.assertEquals("1", s1.element());
    Assert.assertEquals("2", s2.element());
    // we must iterate through the edges, because graph.aConnectingEdge
    // does not respect the direction of the edge!
    EdgeIterator iter = graph.edges();
    while (iter.hasNext()) {
      Edge e = iter.nextEdge();
      if (graph.origin(e) == s2 && graph.destination(e) == s0)
        Assert.assertEquals("action0", e.element());
      else if (graph.origin(e) == s2 && graph.destination(e) == s1)
        Assert.assertEquals("action1", e.element());
      else if (graph.origin(e) == s0 && graph.destination(e) == s2)
        Assert.assertEquals("action2", e.element());
      else
        Assert.assertEquals("actionNone", e.element());
    }
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
    ModelTestCase model = new ModelTestCase(new FSM());
    // remove old coverage listeners
    model.removeAllCoverageMetrics();
    model.addCoverageMetric(metric);
    //    System.out.println("Testing "+metric.getName());
    Assert.assertEquals(0, metric.getCoverage());
    Assert.assertEquals(-1, metric.getMaximum());
    model.buildGraph();
    Assert.assertTrue(metric.getCoverage() > 0);
    Assert.assertEquals(max, metric.getMaximum());
    model.resetCoverageMetrics();
    Assert.assertEquals(0, metric.getCoverage());
    Assert.assertEquals(max, metric.getMaximum());
    Assert.assertEquals(0.0F, metric.getPercentage(), 0.1F);

    for (int i = 0; i < expect.length-1; i += 2) {
      int cov = expect[i+1];
      //      System.out.println("After random walk of length "+expect[i]+
      //          " we expect "+metric.getName()+" = "+cov);
      model.randomWalk(expect[i]);
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
        new int[] {1,0, 2,1, 3,2, 200,10});
  }

}
