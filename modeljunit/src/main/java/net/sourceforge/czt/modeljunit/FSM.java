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
   *  We also report the transition coverage of the model. */
  public static void main(String args[])
  {
    // create our model and a test generation algorithm
    Tester tester = new RandomTester(new FSM());

    // set up our favourite coverage metrics
    CoverageMetric trCoverage = new TransitionCoverage();
    tester.addCoverageMetric(trCoverage);

    // OLD WAY of showing the generated test sequence
    // tester.setVerbosity(2);

    // NEW WAY of outputting verbose messages (uses a listener).
    tester.getModel().addListener("verbose",
        new AbstractListener(tester.getModel())
        {

          public void doneReset(String reason, boolean testing)
          {
            System.out.println("reset(" + testing + ")");
          }

          public void doneTransition(int action, Transition tr)
          {
            System.out.println("done " + tr);
          }
        });

    // finish building the FSM of our model so that we get
    // accurate coverage metrics.
    tester.buildGraph();

    tester.getModel().printMessage("STARTING TESTING");
    trCoverage.clear();

    // generate a test suite of 20 steps
    //tester.reset();
    tester.generate(40);

    tester.getModel().printMessage(trCoverage.getName()+" was "
        +trCoverage.toString());
  }
}
