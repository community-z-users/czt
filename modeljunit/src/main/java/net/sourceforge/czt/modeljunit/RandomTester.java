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
import java.util.Random;

/** Test a system by making random walks through an EFSM model of the system.
 */
public class RandomTester extends Tester
{
  /** During random walk (including buildGraph), this is the
   *  default probability of doing reset() rather than choosing
   *  a random transition.
   */
  public static final double DEFAULT_RESET_PROBABILITY = 0.05;

  /** The probability that doRandomAction does a reset. */
  private double resetProbability_ = DEFAULT_RESET_PROBABILITY;

  /**
   *  Creates a test generator that can generate random walks.
   *
   * @param model  Must be non-null;
   */
  public RandomTester(Model model)
  {
    super(model);
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public RandomTester(FsmModel fsm)
  {
    this(new Model(fsm));
  }

  /** The probability of spontaneously doing a reset rather than
   * a normal transition during random walks etc.
   * @return the reset probability
   */
  public double getResetProbability()
  {
    return resetProbability_;
  }

  /**
   * Set the probability of doing a reset during random walks.
   * Note that the average length of each test sequence will be
   * roughly proportional to the inverse of this probability.
   * <p>
   * If this is set to 0.0, then resets will only be done when
   * we reach a dead-end state (no enabled actions).  This means
   * that if the FSM contains a loop that does not have a path
   * back to the initial state, then the random walks may get
   * caught in that loop forever.  For this reason, a non-zero
   * probability is recommended.
   * </p>
   * <p>
   * The default probability is {@link #DEFAULT_RESET_PROBABILITY}.
   * </p>
   *
   * @param prob    Must be at least 0.0 and less than 1.0.
   */
  public void setResetProbability(double prob)
  {
    if (0.0 <= prob && prob < 1.0)
      resetProbability_ = prob;
    else
      throw new IllegalArgumentException("illegal reset probability: "+prob);
  }

  /** Take any randomly-chosen Action that is enabled.
   *  Returns the number of the Action taken, -1 if all are disabled.
   * @param rand  The Random number generator that controls the choice.
   * @return      The Action taken, or -1 if none are enabled.
   */
  public int doRandomAction()
  {
    int nTrans = model_.getNumActions();
    BitSet tried = new BitSet(nTrans);
    int index = rand_.nextInt(nTrans);
    //System.out.println("random choice is "+index+" out of "+nTrans);
    while (tried.cardinality() < nTrans) {
      while (tried.get(index)) {
        index = rand_.nextInt(nTrans);
        //System.out.println("random RETRY gives "+index);
      }
      tried.set(index); // mark this one as having been tried.
      if (model_.doAction(index)) {
        return index;
      }
    }
    return -1;
  }

  /** Randomly take an enabled transition, or do a reset
   *  with a certain probability (see {@link #getResetProbability()}).
   *
   * @param rand The Random number generator that controls the choice.
   * @return   The number of the transition taken, or -1 for a reset.
   */
  public int doRandomActionOrReset()
  {
    int taken = -1;
    double prob = rand_.nextDouble();
    if (prob < resetProbability_)
      model_.doReset("Random");
    else
    {
      taken = doRandomAction();
      if (taken < 0) {
        model_.doReset("Forced");
      }
    }
    return taken;
  }

  /** Generates a random walk through a finite state machine.
   *  It generates roughly 'length' transitions.
   *  If it has not finished testing, but gets into a state
   *  where there are no Actions enabled, then it will perform
   *  a <code>reset</code> to start from the initial state again.
   *  Each transition is chosen randomly from the set of actions whose
   *  guards are enabled in that state.  There is also a given probability
   *  (see {{@link #setResetProbability(double)} of choosing to do a
   *  reset rather than choosing one of the transitions.
   *
   * @param length The number of transitions to test.
   */

  @Override
  public void generate()
  {
    doRandomActionOrReset();
  }
  
  /** Equivalent to buildGraph(10000). */
  public void buildGraph()
  {
    buildGraph(10000);
  }

  /** Calls {@code generate()} repeatedly until the graph seems to be complete.
   *  The {@code maxSteps} parameter gives an upper bound on the
   *  number of calls to generate, to avoid eternal exploration.
   */
  public void buildGraph(int maxSteps)
  {
    Random old = rand_;
    rand_ = new Random(FIXEDSEED);
    model_.addListener("graph"); // make sure there is a graph listener
    GraphListener graph = (GraphListener)model_.getListener("graph");
    boolean wasTesting = model_.setTesting(false);
    model_.doReset("Buildgraph");
    do {
      generate(); // should be able to set testing=false within generate.
      maxSteps--;
    }
    while (graph.numTodo() > 0 && maxSteps > 0);
    
    model_.setTesting(wasTesting);
    model_.doReset("Buildgraph");
    // restore the original random number generator.
    rand_ = old;
  }
}
