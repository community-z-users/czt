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

/** Simple FSM that is specialized so All Round Trips runs better
 */
public class SpecialFSMNoLoops implements FsmModel
{
  private int state = 0;  // 0..2

  public SpecialFSMNoLoops()
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

  public boolean action0Guard() { return state == 0; }
  public @Action void action0()
  {
    //    System.out.println("action0: " + state + " --> 0");
    state = 1;
  }

  public boolean action1Guard() { return state == 0; }
  public @Action void action1()
  {
    //    System.out.println("action1: " + state + " --> 1");
    state = 2;
  }

  public boolean action2Guard() { return state == 0; }
  public @Action void action2()
  {
    //    System.out.println("action2: " + state + " --> 2");
    state = 3;
  }

  public boolean action3Guard() { return state == 1; }
  public @Action void action3()
  {
    state = 4;
  }

  public boolean action4Guard() { return ((state == 1) || (state == 4) || (state == 10) || (state == 12)); }
  public @Action void action4()
  {
    state = 5;
  } 

  public boolean action5Guard() { return ((state == 2) || (state == 14)); }
  public @Action void action5()
  {
    state = 6;
  }

  public boolean action6Guard() { return state == 2; }
  public @Action void action6()
  {
    state = 7;
  }

  public boolean action7Guard() { return ((state == 2) || (state == 14)); }
  public @Action void action7()
  {
    state = 8;
  }

  public boolean action8Guard() { return ((state == 3) || (state == 20)); }
  public @Action void action8()
  {
    state = 9;
  }

  public boolean action9Guard() { return ((state == 4) || (state == 12)); }
  public @Action void action9()
  {
    state = 10;
  }

  public boolean action10Guard() { return ((state == 10) || (state == 12)); }
  public @Action void action10()
  {
    state = 11;
  }

  public boolean action11Guard() { return state == 10; }
  public @Action void action11()
  {
    state = 12;
  }

  public boolean action12Guard() { return ((state == 6) || (state == 8) || (state == 14)); }
  public @Action void action12()
  {
    state = 13;
  }

  public boolean action13Guard() { return ((state == 7)); }
  public @Action void action13()
  {
    state = 14;
  }

  public boolean action14Guard() { return ((state == 13) || (state == 14)); }
  public @Action void action14()
  {
    state = 15;
  }

  public boolean action15Guard() { return state == 9; }
  public @Action void action15()
  {
    state = 16;
  }

  public boolean action16Guard() { return ((state == 9) || (state == 21)); }
  public @Action void action16()
  {
    state = 17;
  }

  public boolean action17Guard() { return ((state == 9) || (state == 19)); }
  public @Action void action17()
  {
    state = 18;
  }

  public boolean action18Guard() { return ((state == 16) || (state == 17) || (state == 21)); }
  public @Action void action18()
  {
    state = 19;
  }

  public boolean action19Guard() { return ((state == 19) || (state == 21)); }
  public @Action void action19()
  {
    state = 20;
  }

  public boolean action20Guard() { return ((state == 18)); }
  public @Action void action20()
  {
    state = 21;
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
    Tester tester = new RandomTester(new SpecialFSMNoLoops());

    // build the complete FSM graph for our model, just to ensure
    // that we get accurate model coverage metrics.
    tester.buildGraph();

    // set up our favourite coverage metric
    CoverageMetric trCoverage = new TransitionCoverage();
    tester.addListener(trCoverage);

    // ask to print the generated tests
    tester.addListener("verbose");

    // generate a small test suite of 20 steps (covers 4/5 transitions)
    tester.generate(100);

    tester.getModel().printMessage(trCoverage.getName() + " was "
        + trCoverage.toString());
  }
}