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
import java.util.HashMap;

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.Graph;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.jdsl.graph.ref.IncidenceListGraph;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.TransitionCoverage;
import net.sourceforge.czt.modeljunit.coverage.ActionCoverage;
import net.sourceforge.czt.modeljunit.examples.FSM;

/** An attempt at implementing the Pessimistic Player algorithm
 *
 *  @author Pele Douangsavanh
 */
public class LookaheadTester extends Tester
{
  protected GraphListener graph_;

  protected CoverageMetric transitions_;

  protected CoverageMetric actions_;

  private int depth_;

  private boolean complex_;

  /**
   * @return the depth of the recursive lookahead
   */
  public int getDepth()
  {
    return depth_;
  }

  /**
   * Set the lookahead depth.
   * Zero means no lookahead, so the choice will be random.
   *
   * @param depth the depth of the recursive lookahead (0..)
   */
  public void setDepth(int depth_)
  {
    this.depth_ = depth_;
  }

  /**
   *  Creates a test generator that can generate random walks.
   *
   * @param model  Must be non-null;
   */
  public LookaheadTester(Model model)
  {
    super(model);
    model.addListener("graph");
    transitions_ = (CoverageMetric) model.addListener(new TransitionCoverage());
    actions_ = (CoverageMetric) model.addListener(new ActionCoverage());
    graph_ = (GraphListener) model.getListener("graph");
    depth_ = 3;
    complex_ = false;
  }

  /**
   * A convenience constructor that puts a Model wrapper around an FsmModel.
   * @param fsm  Must be non-null.
   */
  public LookaheadTester(FsmModel fsm)
  {
    this(new Model(fsm));
  }

  /**
   * Evaluate the desirability of reaching {@code state}.
   * However, at the top level of recursion (when {@code depth} equals
   * getDepth()), it returns the number of the best action to take.
   * @param state
   * @param depth The depth of lookahead
   * @return A desirability integer, or an action number.
   */
  public int evalState(Object state, int depth)
  {
    if (depth == 0)
      return 0;
    int[] worth = new int[model_.getNumActions()];
    for (int i=0; i < worth.length; i++) {
      worth[i] = Integer.MIN_VALUE;
    }

    InspectableGraph fsmGraph = graph_.getGraph();
    EdgeIterator edges = fsmGraph.edges();

    while (edges.hasNext()) {
      Edge e = edges.nextEdge();
      Object origin = fsmGraph.origin(e).element();
      Object dest = fsmGraph.destination(e).element();
      String actionName = (String) e.element();
      int action = model_.getActionNumber(actionName);
      if (origin.equals(state)
          && graph_.isDone(state, action)) {
        int tempBest = eval(state, action)
            + evalState(dest, depth - 1);
        if (tempBest > worth[action]) {
          worth[action] = tempBest;
        }
      }
    }

    for (int i=0; i<model_.getNumActions(); i++) {
      if (graph_.isTodo(state, i)) {
        worth[i] = 50;
      }
    }

    if (depth == depth_) {
      // now find the best entry in worth
      assert state == model_.getCurrentState();
      int bestAction = -1;
      int bestWorth = Integer.MIN_VALUE;
      for (int i=0; i < model_.getNumActions(); i++) {
        if (model_.isEnabled(i) && worth[i] > bestWorth) {
          bestAction = i;
          bestWorth = worth[i];
        }
      }
      return bestAction;
    }
    else {
      // return sum of all the action worths.
      int result = 0;
      for (int i=0; i < model_.getNumActions(); i++) {
        result += worth[i];
      }
      return result;
    }
  }

  /**
   * Evaluate the desirability of taking the action number
   * {@code action} out of the given state.
   * @param state
   * @param action
   * @return
   */
  public int eval(Object state, int action)
  {
    if (complex_ == true)
      return evalComplex(state, action);
    else
      return evalSimple(state, action);
  }

  public int evalSimple(Object state, int action)
  {
    int result = 0;
    String actionName = model_.getActionName(action);
    if (graph_.isTodo(state, action)) {
      result += 10;
    }

    InspectableGraph fsmGraph = graph_.getGraph();
    EdgeIterator edges = fsmGraph.edges();

    // TODO: see if we can iterate just through the (outgoing) edges of state
    while (edges.hasNext()) {
      Edge e = edges.nextEdge();
      Object origin = fsmGraph.origin(e).element();
      Object dest = fsmGraph.destination(e).element();
      if (origin.equals(state) && e.element().equals(actionName)) {
        Transition tr = new Transition(origin, (String)e.element(), dest);
        Integer done = transitions_.getDetails().get(tr);
        if (done != null) {
          result -= done.intValue();
        }
      }
    }

    /*
    HashMap<Object, Integer> done = new HashMap<Object, Integer>();

    // TODO: see if we can iterate just through the (outgoing) edges of state
    while (edges.hasNext()) {
      Edge e = edges.nextEdge();
      Object origin = fsmGraph.origin(e).element();
      Object dest = fsmGraph.destination(e).element();
      String actionName = (String) e.element();
      int actionNum = model_.getActionNumber(actionName);
      if (origin.equals(state)
          && graph_.isTodo(state, actionNum)) {
        done.put(state, actionNum);
      }
    }

    if ((done.size() == 0) && (graph_.isTodo(state, action)))
      result += 10;
    else
      result -= done.size();
    */
    return result;
  }

  public int evalComplex(Object state, int action)
  {
    int result = evalSimple(state, action);
    // If state has not been visited and action is in toDo set it gets
    // an even higher bias
    if ((actions_.getDetails().get(state) == 0)
        && (graph_.isTodo(state, action)))
      result += 250;
    return result;
  }

  @Override
  public int generate()
  {
    assert depth_ > 0;
    int action = evalState(model_.getCurrentState(), depth_);
    if (action < 0) {
      model_.doReset();
    }
    else {
      if ( ! model_.doAction(action))
        throw new RuntimeException(this.getClass().getName()
            +": could not take action "+action);
    }
    return action;
  }

  public static void main(String[] args) {
    LookaheadTester tester = new LookaheadTester(new FSM());
    tester.addListener(new VerboseListener());
    tester.generate(10);
  }
}
