/**
Copyright (C) 2007 Mark Utting
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

/** Test a system by making greedy walks through an EFSM model of the system.
 *  A greedy random walk gives preference to transitions that have never
 *  been taken before.  Once all transitions out of a state have been taken,
 *  it behaves the same as a random walk.
 *
 *  @author Pele Douangsavanh
 */
public class GreedyTester extends RandomTester
{
  protected GraphListener graph_;

  /**
   *  Creates a test generator that can generate random walks.
   *
   * @param model  Must be non-null;
   */
  public GreedyTester(Model model)
  {
    super(model);
    graph_ = (GraphListener) model_.addListener("graph");
  }


  
  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public GreedyTester(FsmModel fsm)
  {
    super(fsm);
    graph_ = (GraphListener) model_.addListener("graph");
  }
  


  @Override
  public String getName()
  {
    return "Greedy Random Walk";
  }

  @Override
  public String getDescription()
  {
    return "Similar to a random walk, but always takes an unexplored" +
    		" transition if one is enabled in the current state. " +
    		" This gives faster transition coverage initially, then" +
    		" has the same behaviour as a random walk.";
  }

  protected int doGreedyRandomAction()
  {
    // Note that these actions may not be enabled in the current state
    BitSet toDo = graph_.getTodo(model_.getCurrentState());
    if (toDo != null && toDo.cardinality() > 0) {
      // try to choose one of these toDo transitions, randomly
      BitSet tryToDo = (BitSet) toDo.clone();
      while (tryToDo.cardinality() > 0) {
        int nth = rand_.nextInt(tryToDo.cardinality()) + 1;
        assert 1 <= nth;
        assert nth <= tryToDo.cardinality();
        // now set index to the n'th true bit
        int index = -1;
        do {
          index = tryToDo.nextSetBit(index+1);
          assert index >= 0;
          nth--;
        }
        while (nth > 0);
        assert index != -1;
        assert tryToDo.get(index);
        if (model_.doAction(index)) {
          return index;
        }
        else {
          // it was not enabled, so keep trying other toDo transitions
          tryToDo.clear(index);
        }
      }
    }
    // no toDo actions (or none enabled), so just choose any action
    return doRandomAction();
  }

  public int doGreedyRandomActionOrReset()
  {
    int taken = -1;
    double prob = rand_.nextDouble();
    if (prob < getResetProbability()) {
      model_.doReset("Random");
    }
    else {
      taken = doGreedyRandomAction();
      if (taken < 0) {
        model_.doReset("Forced");
      }
    }
    return taken;
  }

  @Override
  public int generate()
  {
    return doGreedyRandomActionOrReset();
  }
}
