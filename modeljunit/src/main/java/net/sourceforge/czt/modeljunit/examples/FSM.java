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

package net.sourceforge.czt.modeljunit.examples;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.RandomTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;

/** Simple example of a finite state machine (FSM) for testing.
 */
public class FSM implements FsmModel
{
  private int state = 0;  // 0..2

  public FSM()
  {
    state = 0;
  }

  public String getState()
  {
    return String.valueOf(state);
  }

  public void reset(boolean testing)
  {
    state = 0;
  }

  public boolean action0Guard() { return state == 2; }
  public @Action void action0()
  {
    //    System.out.println("action0: " + state + " --> 0");
    state = 0;
  }

  public boolean action1Guard() { return state == 2; }
  public @Action void action1()
  {
    //    System.out.println("action1: " + state + " --> 1");
    state = 1;
  }

  public boolean action2Guard() { return state == 0; }
  public @Action void action2()
  {
    //    System.out.println("action2: " + state + " --> 2");
    state = 2;
  }

  public boolean actionNoneGuard() { return state != 1; }
  public @Action void actionNone()
  {
    // leave state the same.
    //    System.out.println("actionNone: " + state + " --> " + state);
  }

  /** This main method illustrates how we can use ModelJUnit
   *  to generate a small test suite.
   *  If we had an implementation of this model that we wanted
   *  to test, we would extend each of the above methods so that
   *  they called the methods of the implementation and checked
   *  the results of those methods.
   *
   *  We also report the transition coverage of the model.
   */
  public static void main(String args[])
  {
    // create our model and a test generation algorithm
    Tester tester = new RandomTester(new FSM());

    // build the complete FSM graph for our model, just to ensure
    // that we get accurate model coverage metrics.
    tester.buildGraph();

    // set up our favourite coverage metric
    CoverageMetric trCoverage = new TransitionCoverage();
    tester.addListener(trCoverage);

    // ask to print the generated tests
    tester.addListener("verbose");

    // generate a small test suite of 20 steps (covers 4/5 transitions)
    tester.generate(20);

    tester.getModel().printMessage(trCoverage.getName() + " was "
        + trCoverage.toString());
  }
}
