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

import junit.framework.Assert;
import junit.framework.AssertionFailedError;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.modeljunit.coverage.CoverageHistory;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.examples.FSM;

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
    RandomTester tester = new RandomTester(new StrangeModel());
    try {
      tester.reset();
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
    RandomTester tester = new RandomTester(new StrangeModel());
    Assert.assertEquals(0.05, tester.getResetProbability());
    tester.setResetProbability(0.0);
    Assert.assertEquals(0.0, tester.getResetProbability());
    tester.setResetProbability(0.99);
    Assert.assertEquals(0.99, tester.getResetProbability());

    try {
      tester.setResetProbability(-0.1);
      Assert.fail("negative reset probability should be illegal");
    }
    catch (IllegalArgumentException ex) {
      // correct
      // check that it is unchanged
      Assert.assertEquals(0.99, tester.getResetProbability());
    }

    try {
      tester.setResetProbability(1.0);
      Assert.fail("reset probability >= 1.0 should be illegal");
    }
    catch (IllegalArgumentException ex) {
      // correct
      // check that it is unchanged
      Assert.assertEquals(0.99, tester.getResetProbability());
    }
  }

  /** Test the effect of reset probability. */
  public static void testResetHigh()
  {
    RandomTester tester = new RandomTester(new FSM());
    tester.buildGraph();
    tester.setResetProbability(0.9);
    CoverageMetric trCover = new TransitionCoverage();
    CoverageHistory hist = new CoverageHistory(trCover,1);
    tester.addListener(hist);
    tester.generate(40);
    // the random walk should choose reset almost all the time
    // so should not get much past the first transition.
    Assert.assertEquals(41, hist.getHistory().size());
    Assert.assertEquals(1, trCover.getCoverage());
  }
}
