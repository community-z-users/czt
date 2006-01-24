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

/** Simple example of a finite state machine (FSM) for testing.
 */
public class FSM implements FsmModel
{
  private int state = 0;  // 0..2
  private boolean testing = false;

  public FSM()
  {
    state = 0;
  }

  public String getState()
  {
    return String.valueOf(state);
  }

  public void reset(boolean startTesting)
  {
    state = 0;
    testing = startTesting;
  }

  public boolean action0Guard() { return state == 2; }
  public @Action void action0()
  {
    if (testing) {
      System.out.println("action0: " + state + " --> 0");
    }
    state = 0;
  }

  public boolean action1Guard() { return state == 2; }
  public @Action void action1()
  {
    if (testing) {
      System.out.println("action1: " + state + " --> 1");
    }
    state = 1;
  }
  
  public boolean action2Guard() { return state == 0; }
  public @Action void action2()
  {
    if (testing) {
      System.out.println("action2: " + state + " --> 2");
    }
    state = 2;
  }

  public boolean actionNoneGuard() { return state != 1; }
  public @Action void actionNone()
  {
    if (testing) {
      // leave state the same.
      System.out.println("actionNone: " + state + " --> " + state);
    }
  }
}
