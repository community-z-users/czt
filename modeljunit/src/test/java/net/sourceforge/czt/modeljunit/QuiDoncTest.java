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

import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;

import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.examples.QuiDonc;

import junit.framework.Assert;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

/**
 * Unit test for ModelJUnit
 */
public class QuiDoncTest extends TestCase
{
  protected static QuiDonc quidonc;
  
  protected static StringWriter output_;
  
  /**
   * Create the test case
   *
   * @param testName name of the test case
   */
  public QuiDoncTest(String testName)
  {
    super(testName);
  }

  public void setUp()
  {
    output_ = new StringWriter();
    quidonc = new QuiDonc(new PrintWriter(output_));
  }

  /**
   * @return the suite of tests being tested
   */
  public static Test suite()
  {
    return new TestSuite(QuiDoncTest.class);
  }

  public static void testEnabled()
  throws FileNotFoundException
  {
    Tester tester = new RandomTester(quidonc);
    GraphListener graph = tester.buildGraph();
    //    model.printGraphDot("QuiDonc.dot");
    // NOTE: with the State+timeouts getState, it has 11 vertices, 37 edges.
    Assert.assertEquals(5, graph.getGraph().numVertices());
    int numEdges = graph.getGraph().numEdges();
    output_.write("QuiDonc has "+numEdges+" edges.\n");
    // should be 18 transitions, but we cannot find some of the non-det
    // wait transitions that are enabled only on the third wait call.
    Assert.assertEquals(17, graph.getGraph().numEdges());
    // fsmDoAction(fsmGetAction("dial"));
    // System.out.println(output_.toString());
  }

  /** This tests a random walk, plus transition coverage */
  public static void testRandomWalk()
  {
    output_.write("STARTING RANDOM\n");
    Tester tester = new RandomTester(quidonc);
    CoverageHistory metric = new CoverageHistory(new TransitionCoverage(), 1);
    tester.addListener(metric);
    tester.generate(100);
    int coverage = metric.getCoverage();
    List<Integer> hist = metric.getHistory();
    Assert.assertNotNull(hist);
    output_.write("transhist="+metric.toCSV()+"\n");
    Assert.assertEquals(16, coverage);
    Assert.assertEquals(-1, metric.getMaximum());
    Assert.assertEquals("Incorrect history size.", 101, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
    Assert.assertEquals(new Integer(coverage), hist.get(hist.size() - 1));
    // System.out.println(output_.toString());
  }

  /** This tests a greedy random walk, plus transition coverage */
  public static void testGreedyRandomWalk()
  {
    output_.write("STARTING GREEDY\n");
    Tester tester = new GreedyTester(new QuiDonc());
    CoverageHistory metric = new CoverageHistory(new TransitionCoverage(), 1);
    tester.addListener(metric);
    tester.generate(100);
    int coverage = metric.getCoverage();
    List<Integer> hist = metric.getHistory();
    Assert.assertNotNull(hist);
    output_.write("transhist="+metric.toCSV()+"\n");
    Assert.assertEquals(17, coverage);
    Assert.assertEquals(17, metric.getMaximum());
    Assert.assertEquals("Incorrect history size.", 101, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
    Assert.assertEquals(new Integer(coverage), hist.get(hist.size() - 1));
    // System.out.println(output_.toString());
  }

  /** This tests an all-round-trips walk, plus transition coverage */
  public static void testAllRoundTrips()
  {
    output_.write("STARTING ALL ROUND TRIPS\n");
    Tester tester = new AllRoundTester(new QuiDonc());
    CoverageHistory metric = new CoverageHistory(new TransitionCoverage(), 1);
    tester.addCoverageMetric(metric);
    tester.generate(100);
    int coverage = metric.getCoverage();
    List<Integer> hist = metric.getHistory();
    Assert.assertNotNull(hist);
    output_.write("transhist="+metric.toCSV()+"\n");
    Assert.assertEquals(12, coverage);
    Assert.assertEquals(-1, metric.getMaximum());
    // TODO: Assert.assertEquals("Incorrect history size.", 101, hist.size());
    Assert.assertEquals(new Integer(0), hist.get(0));
    Assert.assertEquals(new Integer(coverage), hist.get(hist.size() - 1));
    // System.out.println(output_.toString());
  }
}
