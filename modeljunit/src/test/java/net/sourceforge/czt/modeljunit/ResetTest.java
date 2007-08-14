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
import junit.framework.AssertionFailedError;
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

/**
 * Unit test for ModelJUnit
 */
public class ResetTest extends TestCase
{
  /**
   * Create the test case
   *
   * @param testName name of the test case
   */
  public ResetTest(String testName)
  {
    super(testName);
  }

  /**
   * @return the suite of tests being tested
   */
  public static Test suite()
  {
    return new TestSuite(ResetTest.class);
  }

  /** This model counts up from 0..10.
   *  But its reset is non-deterministic.
   * @author marku
   *
   */
  protected static class StrangeModel implements FsmModel
  {
    private int resets = 0;
    private int state = 0;

    public Object getState()
    {
      return ""+state;
    }

    /** Non-det reset. */
    public void reset(boolean testing)
    {
      resets++;
      state = resets;
    }

    public @Action void Incr()
    {
      state++;
      if (state > 10)
        state = 10;
    }
  }


  /** This model has no transitions and getState returns null.
   * @author marku
   *
   */
  protected static class NullModel implements FsmModel
  {
    public Object getState()
    {
      return null;
    }

    public void reset(boolean testing)
    {
    }

    public @Action void action()
    {
    }
  }


  public static void testNonDetReset()
  {
    ModelTestCase model = new ModelTestCase(new StrangeModel());
    try {
      model.doReset(true);
      Assert.fail("PROBLEM: non-det reset was not detected.");
    }
    catch (AssertionFailedError ex) {
      // Good.  The non-det reset was detected.
      Assert.assertTrue(ex.getMessage().startsWith("Model error: reset"));
    }
  }

  public static void testNullReset()
  {
    try {
      ModelTestCase model = new ModelTestCase(new NullModel());
      model.doReset(true);
      Assert.fail("PROBLEM: null reset was not detected.");
    }
    catch (AssertionFailedError ex) {
      Assert.assertTrue(ex.getMessage().startsWith("Model Error: getState() must be non-null"));
    }
  }

  /** Test the getting/setting of reset probability */
  public static void testResetProbability()
  {
    ModelTestCase model = new ModelTestCase(new StrangeModel());
    Assert.assertEquals(0.05, model.getResetProbability());
    model.setResetProbability(0.0);
    Assert.assertEquals(0.0, model.getResetProbability());
    model.setResetProbability(0.99);
    Assert.assertEquals(0.99, model.getResetProbability());

    try {
      model.setResetProbability(-0.1);
      Assert.fail("negative reset probability should be illegal");
    }
    catch (IllegalArgumentException ex) {
      // correct
      // check that it is unchanged
      Assert.assertEquals(0.99, model.getResetProbability());
    }

    try {
      model.setResetProbability(1.0);
      Assert.fail("reset probability >= 1.0 should be illegal");
    }
    catch (IllegalArgumentException ex) {
      // correct
      // check that it is unchanged
      Assert.assertEquals(0.99, model.getResetProbability());
    }
  }

  /** Test the effect of reset probability. */
  public static void testResetHigh()
  {
    ModelTestCase model = new ModelTestCase(new FSM());
    model.buildGraph();
    model.setResetProbability(0.9);
    CoverageMetric trCover = new TransitionCoverage();
    CoverageHistory hist = new CoverageHistory(trCover,1);
    model.addCoverageMetric(hist);
    model.randomWalk(40);
    // the random walk should choose reset almost all the time
    // so should not get past the first transition.
    Assert.assertEquals(41, hist.getHistory().size());
    Assert.assertEquals(3, trCover.getCoverage());
  }
}
