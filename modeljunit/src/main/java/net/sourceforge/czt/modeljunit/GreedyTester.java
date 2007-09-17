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

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Random;

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
    model.addListener("graph");
    graph_ = (GraphListener) model.getListener("graph");
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public GreedyTester(FsmModel fsm)
  {
    this(new Model(fsm));
  }


  protected int doGreedyRandomAction()
  {
    // System.out.println("Currently in state: " + fsmState);
    /*
     BitSet of the actions that need to be done for the current state

     True, if action has not been done and is enabled
     False, Otherwise

     Null, if terminal state or state has no more unvisted transitions
     Non-Null, otherwise
     */
    BitSet toDo = graph_.getTodo(model_.getCurrentState());
    /*
     BitSet of the actions have been done for the current state

     True, if action has been done
     False, Otherwise

     Null, if terminal state or state has not been visited
     Non-Null, otherwise
     */
    BitSet done = graph_.getDone(model_.getCurrentState());
    // Indexes of the actions that need to be done
    ArrayList<Integer> indexToDo = new ArrayList<Integer>();

    // If terminal state we must force a reset so return -1
    if (toDo == null && done == null)
      return -1;
    else if (toDo == null && done != null) {
      // If all actions of the state have been done just choose one randomly
      return doRandomAction();
    }

    // System.out.println("todo cardinality: " + toDo.cardinality());

    if (toDo.cardinality() == 0) {
      // If all actions of the state have been done just choose one randomly
      return doRandomAction();
    }
    else if (toDo.cardinality() == 1) {
      // Get the index of the only set bit in the toDo Bitset
      int index = toDo.nextSetBit(0);
      if (model_.doAction(index)) {
        // If action is done return the action that was done
        return index;
      }
    }
    else {
      // Iterate over all true bits and put their indexes into a list
      for (int i = toDo.nextSetBit(0); i >= 0; i = toDo.nextSetBit(i + 1)) {
        indexToDo.add(i);
      }
      // Randomly generate an index from 0 to size() of indexToDo - 1
      int index = rand_.nextInt(indexToDo.size());
      // System.out.println("index: " + index);
      if (model_.doAction(indexToDo.get(index))) {
        // If action is done return the action that was done
        return indexToDo.get(index);
      }
    }
    return -1;
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
