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

import net.sourceforge.czt.modeljunit.timing.TimedFsmModel;
import net.sourceforge.czt.modeljunit.timing.TimedModel;

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
    super(fsm);
  }
  


  public String getName()
  {
    return "Random Walk";
  }

  public String getDescription()
  {
    return "Walks through the model, choosing a random enabled action out of" +
    		" each state.  It also performs random resets occasionally" +
    		" (with a default probability of 5%), to ensure that all" +
    		" paths from the initial state will eventually be explored.";
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
   * @return      The Action taken, or -1 if none are enabled.
   */
  public int doRandomAction()
  {
    int nTrans = model_.getNumActions();
    BitSet tried = new BitSet(nTrans);
    int index = rand_.nextInt(nTrans);
    //System.out.println("DEBUG: random choice is "+index+" out of "+nTrans
    //    +" tried.card="+tried.cardinality());
    while (tried.cardinality() < nTrans) {
      while (tried.get(index)) {
        index = rand_.nextInt(nTrans);
        //System.out.println("DEBUG: random RETRY gives "+index);
      }
      tried.set(index); // mark this one as having been tried.
      if (model_.doAction(index)) {
        //System.out.println("DEBUG: done action "+index);
        return index;
      }
    }
    return -1;
  }

  /** Randomly take an enabled transition, or do a reset
   *  with a certain probability (see {@link #getResetProbability()}).
   *
   *  If this method is called in a state where
   *  there are no Actions enabled, then it will perform
   *  a <code>reset</code> to start from the initial state again.
   *
   * @return   The number of the transition taken, or -1 for a reset.
   */
  public int doRandomActionOrReset()
  {
    int taken = -1;
    double prob = rand_.nextDouble();
    //System.out.println("DEBUG: RESET if "+prob+" < "+resetProbability_);
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

  /** Generates one step of a random walk through the model.
   *  This calls {@link #doRandomActionOrReset()}.
   */

  @Override
  public int generate()
  {
    return doRandomActionOrReset();
  }
}
