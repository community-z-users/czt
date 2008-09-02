/**
 Copyright (C) 2008 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
 (at your option) any later version.

 The CZT project is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with CZT; if not, write to the Free Software
 Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.modeljunit.examples;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.LookaheadTester;
import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.VerboseListener;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.examples.ecinema.ECinema;

/** The performs some simple experiments on various test generation
 *  algorithms to compare the average size of the test suites that
 *  they must generate to achieve 100% transition coverage.
 *  
 *  TODO: could report the standard deviation as well.
 */
public class SizeExperiments 
{
  /** Number of times to repeat each experiment, to get an average. */
  public static final double RUNS = 100.0;

  /** Measures how long it takes tester to satisfy all-transitions coverage.
   *  It repeats this experiment RUNS times and returns the average.
   * @param tester
   * @return average number of test steps required to cover all transitions.
   */
  public static double allTransitions(Tester tester)
  {
    GraphListener graph = tester.buildGraph(100000);
    //tester.addListener(new VerboseListener()); //if you want to see the tests
    CoverageMetric trans = tester.addCoverageMetric(new TransitionCoverage());
    int total = 0;
    tester.setRandom(new Random(Tester.FIXEDSEED));
    for (int run=0; run<RUNS; run++) {
      int steps = 0;
      trans.clear();
      graph.clearDoneTodo();
      tester.reset();
      while (trans.getPercentage() < 100.0) {      
        tester.generate();
        steps++;
      }
      // Uncomment the next line if you want to see every experiment.
      //System.out.println("coverage = "+trans+" in "+steps+" steps");
      total += steps;
    }
    return total / RUNS;
  }

  /** An example of generating tests from this model. */
  public static void main(String[] args)
  {
    FsmModel model = new SimpleSet();
    List<Tester> testers = new ArrayList<Tester>();
    testers.add(new RandomTester(model));
    testers.add(new GreedyTester(model));
    testers.add(new LookaheadTester(model));

    for (Tester tester : testers) {
      double average = allTransitions(tester);
      System.out.println(tester.getName()+": "+average+" average.");
    }
  }
}
