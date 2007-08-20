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

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.Graph;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.jdsl.graph.ref.IncidenceListGraph;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;


/** This ModelListener builds a graph of the observed parts of the model.
 *  Note that it is some other class (typically a Tester subclass) that
 *  determines which parts of the model are explored.
 *
 *  As well as building the graph, this listener also keeps track of
 *  which paths have not yet been explored.
 */
public class GraphListener implements ModelListener
{
  protected Model model_;

  public GraphListener(Model model)
  {
    model_ = model;
    startBuildGraph();
  }

  /** The graph of all the states and transitions of this FSM.
   *  Here are several invariants of the graph structures:
   *  <ul>
   *    <li>fsmState is the current state we are exploring.</li>
   *    <li>fsmTodo_ does not contain any empty BitSets.</li>
   *    <li>fsmDone_ can contain empty BitSets and its domain is
   *        the same as the domain of fsmVertex_.</li>
   *    <li>for every transition (s0,action,s1) in the FSM, exactly
   *    one of the following is true:
   *    <ol>
   *      <li>s0 has not yet been visited, or</li>
   *      <li>fsmTodo_(s0) has a bit set for action, or</li>
   *      <li>(s0,action,s1) has been added to fsmGraph_ and
   *          fsmDone_(s0) has a bit set for action.</li>
   *    <ol>
   *  </ul>
   */
  //@invariant fsmGraph_!=null ==> fsmClass!=null;
  private Graph fsmGraph_;

  /** A map from fsm states to the corresponding vertex of fsmGraph_. */
  //@invariant fsmVertex_==null <==> fsmGraph_==null;
  // invariant (obj,vertex) in fsmVertex_ <==> vertex.element()==obj;
  private Map<Object,Vertex> fsmVertex_;

  /** Records the (state,action) pairs that have been explored. */
  private Map<Object,BitSet> fsmDone_;

  /** Records the (state,action) pairs that have not been explored. */
  private Map<Object,BitSet> fsmTodo_;

  /** Returns true when the graph seems to be completely explored.
   *  That is, when numTodo()==0.  However, this is only a heuristic,
   *  and it is quite possible that a few more non-deterministic or
   *  rarely-enabled transitions will be found by further test generation.
   *
   * @return
   */
  public boolean isComplete()
  {
    return fsmTodo_.size() == 0;
  }

  /** Returns the number of unexplored paths/branches in the graph.
   *
   *  TODO: could make this efficient by caching or maintaining the sum
   *       of the number of todo bits.
   */
  public int numTodo()
  {
    int result = 0;
    for (BitSet bits : fsmTodo_.values()) {
      result += bits.cardinality();
    }
    return result;
  }

  /** True if the guard of the given action was once true in the given
   *  state, but that action has not yet been executed from that state.
   * @param state   A non-null state of the model.
   * @param action  The number of one of the actions of the model.
   * @return
   */
  public boolean isTodo(Object state, int action)
  {
    BitSet todo = fsmTodo_.get(state);
    if (todo == null)
      return false;
    return todo.get(action);
  }

  /** True if the given action has been executed from the given state.
   * @param state   A non-null state of the model.
   * @param action  The number of one of the actions of the model.
   * @return
   */
  public boolean isDone(Object state, int action)
  {
    BitSet done = fsmDone_.get(state);
    if (done == null)
      return false;
    return done.get(action);
  }

  /** Returns the graph of the FSM model.
   *  Note that the graph may be incomplete
   *  (call buildGraph to explore the graph thoroughly).
   */
  public InspectableGraph getGraph()
  {
    return fsmGraph_;
  }

  /** Maps a state to a vertex object of the FSM graph.
   */
  public Vertex getVertex(Object state)
  {
    return fsmVertex_.get(state);
  }

  public void printProgress(int importance, String msg)
  {
    // model_.printMessage(msg);
  }

  /** Returns the model that is being used to generate tests */
  @Override
  public Model getModel()
  {
    return model_;
  }

  /** Starts to build the FSM graph by exploring the fsm object.
   *  This assumes that the current fsmState is the initial state.
   *  That is, a reset has just been done.
   */
  protected void startBuildGraph()
  {
    Object curr = model_.getCurrentState();
    assert curr != null;
    fsmGraph_ = new IncidenceListGraph();
    fsmVertex_ = new HashMap<Object,Vertex>();
    fsmDone_ = new HashMap<Object,BitSet>();
    fsmTodo_ = new HashMap<Object,BitSet>();
    // set up the initial state
    Vertex initial = fsmGraph_.insertVertex(curr);
    assert initial != null;
    printProgress(3, "buildgraph: start with vertex for initial state "+curr);
    fsmVertex_.put(curr, initial);
    fsmDone_.put(curr, new BitSet());
    BitSet enabled = model_.enabledGuards();
    if (enabled.isEmpty())
      throw new FsmException("Initial state has no actions enabled.");
    fsmTodo_.put(curr, enabled);
  }

  /** Finish building the graph.
   *  That is, keep exploring until all enabled actions in
   *  all reachable states that have explored.
   *  Of course, this may not have built ALL the graph if some
   *  guards are enabled sporadically in a given state, or if
   *  some transitions are non-deterministic.
   *
   *  <p>
   *  Note that this method traverses the graph as it explores its
   *  shape, and this traversal is likely to increase any coverage
   *  statistics that are being recorded.  For example, transition
   *  coverage will normally be 100% after this method returns.
   *  If you want to measure the coverage of a short traversal,
   *  you should call this method to explore the graph, then reset
   *  the coverage measures to zero <em>before</em> doing the traversal.
   *  </p>
   *
   *  @param rand  A random generator to choose the exploration path.
   *  @return true if the graph seems to be completely built.
   */
  /*
   * TODO: implement this.  (Pass it an arbitrary Tester?)
   *
  public boolean buildGraph(Random rand, int maxTransitions)
  {
    int maxLen = maxTransitions;
    while (fsmTodo_.size() > 0 && maxLen > 0) {
      maxLen--;
      doRandomActionOrReset(rand, false);
    }
    for (CoverageMetric cm : fsmCoverage) {
      cm.setModel(fsmGraph_, fsmVertex_);
    }
    if (fsmTodo_.size() == 0) {
      // we seem to have explored all paths
      printProgress(1, "FSM has "+this.fsmGraph.numVertices()
          +" states and "+this.fsmGraph.numEdges()+" transitions.");
      return true;
    }
    else {
        printProgress(1, "BuildGraph still has " + fsmTodo_.size()
            + " unexplored paths after " + maxTransitions
            + " transitions.  FSM too big?");
        return false;
    }
  }
  */

  /** Equivalent to buildGraph(new Random(FIXEDSEED), 10000). */
  /*
  public boolean buildGraph(Random rand)
  {
    return buildGraph(new Random(FIXEDSEED), 10000);
  }
  */

  /** Equivalent to buildGraph(new Random(FIXEDSEED)). */
  /*
  public boolean buildGraph()
  {
    return buildGraph(new Random(FIXEDSEED));
  }
  */

  /** Saves the FSM graph into the given file, in DOT format.
   *  The DOT format can be converted into many other graphical formats,
   *  including xfig, postscript, jpeg etc. by using the 'dot' or 'neato'
   *  tools, which are freely available from http://www.graphviz.org.
   *  This method should only be called after buildGraph has built the graph.
   * @param filename  The filename should end with ".dot".
   */
  public void printGraphDot(String filename)
  throws FileNotFoundException
  {
    if (fsmGraph_ == null)
      throw new IllegalStateException("Graph not built yet.  Call buildGraph.");
    PrintWriter output = new PrintWriter(filename);
    String shortName = model_.getModelName();
    shortName = shortName.substring(shortName.lastIndexOf('.')+1);
    output.println("digraph "+shortName);
    output.println("{");
    EdgeIterator edges = fsmGraph_.edges();
    while (edges.hasNext()) {
      Edge e = edges.nextEdge();
      Object origin = fsmGraph_.origin(e).element();
      Object dest = fsmGraph_.destination(e).element();
      String action = (String) e.element();
      output.println("  "+stateName(origin)+" -> "+stateName(dest)
          +"  [label=\""+action+"\"];");
    }
    output.println("}");
    output.close();
  }

  /** Converts a state into a name.
   *  It calls toString on the state, and then adds quotes around
   *  the string if it is not a Java identifier.
   *
   * @param str
   * @return
   */
  public static String stateName(Object state)
  {
    String str = state.toString();
    if (str.matches("[a-zA-Z][a-zA-Z0-9_]*"))
      return str;
    else
      return "\"" + str.replaceAll("\"", "\\\"") + "\"";
  }

  @Override
  public void doneGuard(Object state, int action, boolean enabled, int value)
  {
  }

  @Override
  public void doneReset(String reason, boolean testing)
  {
  }

  /** Records a transition in the graph, if it is not already there.
   *  This internal method should be called by doAction, so that
   *  it can analyze/record every transition.  It is quite like
   *  a coverage listener, but I decided to make it more built-in
   *  because the graph is so fundamental to model-based testing.
   * @param tr  A possibly new transition (and state).
   */
  @Override
  public void doneTransition(int action, Transition tr)
  {
    Object oldState = tr.getStartState();
    Vertex oldVertex = fsmVertex_.get(oldState);
    assert oldVertex != null;  // we must have already visited it.
    String actionName = tr.getAction();
    Object newState = tr.getEndState();
    assert newState == model_.getCurrentState();  // we should still be inside doAction.
    BitSet enabled = model_.enabledGuards();
    // see if this newState is an unknown one.
    Vertex newVertex = fsmVertex_.get(newState);
    if (newVertex == null) {
      // we have reached a new state, so add & analyze it.
      newVertex = fsmGraph_.insertVertex(newState);
      fsmVertex_.put(newState, newVertex);
      fsmDone_.put(newState, new BitSet());
      printProgress(3, "buildgraph: Added vertex for state "+newState);
      if ( ! enabled.isEmpty())
        fsmTodo_.put(newState, enabled);
    }
    else {
      // see if we need to add some bits to fsmTodo_.
      enabled.andNot(fsmDone_.get(newState));
      if ( ! enabled.isEmpty()) {
        BitSet oldTodo = fsmTodo_.get(newState);
        if (oldTodo == null)
          fsmTodo_.put(newState, enabled);
        else
          oldTodo.or(enabled);
      }
    }
    // see if fsmGraph_ already contains this edge.
    boolean present = false;
    EdgeIterator edges = fsmGraph_.connectingEdges(oldVertex, newVertex);
    while (edges.hasNext()) {
      Edge edge = edges.nextEdge();
      if (edge.element().equals(actionName)
          && fsmGraph_.origin(edge) == oldVertex
          && fsmGraph_.destination(edge) == newVertex) {
        present = true;
        break;
      }
    }
    if ( ! present) {
      fsmGraph_.insertDirectedEdge(oldVertex, newVertex, actionName);
      fsmDone_.get(oldState).set(action);
      printProgress(3, "buildgraph: Added edge ("+oldState+","
          +actionName+","+newState+")");

      // See if we can reduce the fsmTodo_ flags of oldState
      BitSet bset = fsmTodo_.get(oldState);
      if (bset != null) {
        bset.clear(action);
        if (bset.isEmpty()) {
          fsmTodo_.remove(oldState);
          if (isComplete()) {
            // tell all the listeners about the graph
            printProgress(2, "completed graph, so calling setModel");
            for (ModelListener listen : model_.getListeners().values()) {
              if (listen instanceof CoverageMetric) {
                ((CoverageMetric)listen).setModel(fsmGraph_, fsmVertex_);
              }
            }
          }
        }
      }
    }
  }

  @Override
  public void failure(Exception ex)
  {
  }

  @Override
  public void startAction(Object state, int action, String name)
  {
    // TODO Auto-generated method stub

  }
}
