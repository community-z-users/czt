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

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.Tester;

/** A simple EFSM model of the Qui-Donc service.
 *  Qui-Donc is a service of France Telecom that allows you
 *  to ring up, enter a telephone number and find which subscriber
 *  owns that telephone number and what is their address.
 */
public class QuiDonc implements FsmModel
{
  public enum State
    { Start, // not yet connected to the Qui-Donc service.
      Star,  // waiting for the initial '*'.
      Enter, // waiting for a telephone number to be entered.
      Emerg, // after explaining the emergency number, waiting for '*'.
      Info   // ready to give information about the subscriber.
    };
  private State currState; // the current state of the system.
  private int timeouts;    // on the third timeout, we hang up.
  private PrintWriter out; // output stream for test instructions

  public String _STAR = "Please press the star key.";
  public String WELCOME  = "Welcome to Qui-Donc.  "+_STAR;
  public String NOTALLOW = "Your telephone does not allow access to the Qui-Donc service.";
  public String ENTER    = "Please enter the 10-digit telephone number of the subscriber you are looking for, followed by the hash key.";
  public String ERROR    = "Invalid number entered.  Please enter another number, followed by the hash key.";
  public String FIRE     = "18 is the emergency number for the Fire Brigade.  If you want to do another search, press star.";
  public String SORRY    = "Sorry.  The number 03 81 12 34 57 does not appear in the white pages.  "+ENTER;
  public String INFO     = "Press 1 to spell the name, press 2 to hear the address, or press star for a new search.";
  public String NAME     = "The number 03 81 12 34 56 corresponds to Renard, K. J.  "+INFO;
  public String SPELL    = "Renard is spelt R, E, N, A, R, D.  "+INFO;
  public String ADDR     = "The address of Renard, K. J. is 45 rue de Vesoul, Besan\u00E7on.  "+INFO;
  public String BYE      = "Thank you for using the Qui-Donc service.";

  public QuiDonc()
  {
    this(new PrintWriter(System.out));
  }

  public QuiDonc(PrintWriter out0)
  {
    out = out0;
    timeouts = 0;
    currState = State.Start;
  }

  public String getState()
  {
    return currState.toString(); // + timeouts;
  }

  public void reset(boolean testing)
  {
    timeouts = 0;
    currState = State.Start;
  }

  public boolean dialGuard() { return currState == State.Start; }
  public @Action void dial()
  {
    out.println("dial/"+WELCOME);
    currState = State.Star;
    timeouts = 0;
  }

  /** We call this wait_, to avoid a clash with Java's Object.wait(). */
  public @Action void wait_()
  {
    timeouts++;
    if (timeouts >= 3
        || currState == State.Emerg
        || currState == State.Start) {
      if (currState == State.Star)
        out.println("wait/"+NOTALLOW);
      else
        out.println("wait/"+BYE);
      currState = State.Start;
      timeouts = 0;
    }
    else
      out.println("wait/...(Repeat Message)...");
  }

  public boolean starGuard()
  { return currState == State.Star
        || currState == State.Emerg
        || currState == State.Info; }
  public @Action void star()
  {
    out.println("*/"+ENTER);
    currState = State.Enter;
    timeouts = 0;
  }

  public boolean badGuard() { return currState == State.Enter; }
  public @Action void bad()
  {
    out.println("bad/"+ERROR);
    // leave state the same, but reset timeouts.
    timeouts = 0;
  }

  public boolean num18Guard() { return currState == State.Enter; }
  public @Action void num18()
  {
    out.println("18/"+FIRE);
    currState = State.Emerg;
    timeouts = 0;
  }

  public boolean num1Guard() { return currState == State.Enter; }
  public @Action void num1()
  {
    out.println("num1/"+SORRY);
    // leave state the same, but reset timeouts.
    timeouts = 0;
  }

  public boolean num2Guard() { return currState == State.Enter; }
  public @Action void num2()
  {
    out.println("num2/"+NAME);
    currState = State.Info;
    timeouts = 0;
  }

  public boolean key1Guard() { return currState == State.Info; }
  public @Action void key1()
  {
    out.println("1/"+SPELL);
    // leave state the same, but reset timeouts.
    timeouts = 0;
  }

  public boolean key2Guard() { return currState == State.Info; }
  public @Action void key2()
  {
    out.println("2/"+ADDR);
    // leave state the same, but reset timeouts.
    timeouts = 0;
  }


  /** Convenience method for the interactive interface. */
  public static void checkGuard(QuiDonc quidonc, boolean guard)
  {
    if ( ! guard)
      quidonc.out.println("WARNING: that action is not enabled, but we'll do it anyway...");
  }

  /** An interactive interface to QuiDonce, for illustration purposes. */
  public static void main(String[] args) throws IOException
  {
    QuiDonc quidonc = new QuiDonc();

    // In order to read a line at a time from System.in,
    // which is type InputStream, it must be wrapped into
    // a BufferedReader, which requires wrapping it first
    // in an InputStreamReader.
    // Note the "throws" clause on the enclosing method (main).
    InputStreamReader isr = new InputStreamReader(System.in);
    BufferedReader input = new BufferedReader(isr);

    quidonc.out.println("This program allows you to explore the QuiDonc model interactively.");
    quidonc.out.println("The following inputs are possible (or type 'graph' to generate the FSM):");
    quidonc.out.println("  dial,*,1,2,wait,18#,0381111111#,0381222222#,...");
    // Read and print lines in a loop.
    // Terminate with control-Z (Windows) or control-D (other)
    while (true) {
      quidonc.out.print(quidonc.getState()+"> ");
      String line = input.readLine();
      if (line == null)
        break;
      if (line.equals("graph")) {
        quidonc.out.println("Building FSM graph...");
        Tester tester = new GreedyTester(quidonc);
        GraphListener graph = tester.buildGraph();
        graph.printGraphDot("QuiDonc.dot");
        quidonc.out.println("Printed FSM graph to QuiDonc.dot.");
        quidonc.out.println("Use dotty or dot from http://www.graphviz.org"
            + " to view/transform the graph.");
      }
      else if (line.equals("dial")) {
        checkGuard(quidonc, quidonc.dialGuard());
        quidonc.dial();
      }
      else if (line.equals("*")) {
        checkGuard(quidonc, quidonc.starGuard());
        quidonc.star();
      }
      else if (line.equals("1")) {
        checkGuard(quidonc, quidonc.key1Guard());
        quidonc.key1();
      }
      else if (line.equals("2")) {
        checkGuard(quidonc, quidonc.key2Guard());
        quidonc.key2();
      }
      else if (line.equals("wait")) {
        //checkGuard(quidonc.wait_Guard());
        quidonc.wait_();
      }
      else if (line.equals("18#")) {
        checkGuard(quidonc, quidonc.num18Guard());
        quidonc.num18();
      }
      else if (line.equals("0381111111#")) {
        checkGuard(quidonc, quidonc.num1Guard());
        quidonc.num1();
      }
      else if (line.equals("0381222222#")) {
        checkGuard(quidonc, quidonc.num2Guard());
        quidonc.num2();
      }
      else {
        checkGuard(quidonc, quidonc.badGuard());
        quidonc.bad();
      }
    }
  }
}
