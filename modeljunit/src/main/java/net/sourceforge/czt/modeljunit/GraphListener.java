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
 *  which paths have not yet been explored.  Internally, it keeps track
 *  of two bitsets for each node/state.  The 'done_' set records the 
 *  outgoing transitions that have been taken/explored since the last
 *  call to clearDoneTodo().  The 'wasEnabled_' set records the actions that
 *  have been observed to have true guards at some point since the last
 *  call to clearDoneTodo() (this includes implicitly true guards, where the
 *  action has no explicit guard).
 */
public class GraphListener extends AbstractListener
{
  public String getName()
  {
    return "graph";
  }

  /** The graph of all the states and transitions of this FSM.
   *  Here are several invariants of the graph structures:
   *  <ul>
   *    <li>fsmState is the current state we are exploring.</li>
   *    <li>for any state S and action A, 
   *        isDone(S,A) implies wasEnabled_.get(S).get(A).</li>
   *    <li>the domains of done_ and wasEnabled_ are a subset of the
   *        domain of vertex_.</li>
   *    <li>for any transition (S1,A,S2), isDone(S1,A) implies that
   *        the transition is in graph_.</li>
   *    <ol>
   *  </ul>
   */
  //@invariant fsmGraph_!=null ==> fsmClass!=null;
  private Graph fsmGraph_;

  /** A map from fsm states to the corresponding vertex of fsmGraph_. */
  //@invariant fsmVertex_==null <==> fsmGraph_==null;
  // invariant (obj,vertex) in fsmVertex_ <==> vertex.element()==obj;
  private Map<Object,Vertex> fsmVertex_;

  /** Records the (state,action) pairs that have been explored.
   *  There is an entry in this map for every state that has been visited.
   */
  private Map<Object,BitSet> done_;

  /** Records the (state,action) pairs that have had true guard. */
  private Map<Object,BitSet> wasEnabled_;

  /** This remembers whether this graph has been complete. */
  private boolean complete_ = false;
  
  /** Returns true after the graph seems to be completely explored.
   *  That is, when numTodo()==0 at some point in the past.
   *  However, this is only a heuristic,
   *  and it is quite possible that a few more non-deterministic or
   *  rarely-enabled transitions will be found by further test generation.
   *
      * @return true if numTodo() was or is 0.
   */
  public boolean isComplete()
  {
    return complete_;
  }

  /** Returns the number of unexplored paths/branches in the graph.
   *
   *  TODO: make this efficient by maintaining the sum
   *       of the number of done_ and wasEnabled_ bits
   *       and returning the difference.
   */
  public int numTodo()
  {
    int result = 0;
    for (Map.Entry<Object, BitSet> e : wasEnabled_.entrySet()) {
      BitSet enabled = e.getValue();
      BitSet done = done_.get(e.getKey());
      result += enabled.cardinality() - (done==null ? 0 : done.cardinality());
    }
    return result;
  }

  /** True if the guard of the given action was once true in the given
   *  state, but that action has not yet been executed from that state.
   * @param state   A non-null state of the model.
   * @param action  The number of one of the actions of the model.
   * @return true if no transition (state, action, _) has been taken yet.
   */
  public boolean isTodo(Object state, int action)
  {
    BitSet enabled = wasEnabled_.get(state);
    if (enabled == null)
      return false;
    BitSet done = done_.get(state);
    return enabled.get(action) && (done==null || ! done.get(action));
  }

  /**
   *  Returns a bitset of all the TODO bits for this state.
   *  Callers can mutate the returned BitSet.
   * @param state
   * @return A copy of a non-null BitSet.
   */
  public BitSet getTodo(Object state)
  {
    BitSet enabled = wasEnabled_.get(state);
    if (enabled == null) {
      return new BitSet();
    }
    BitSet result = (BitSet) enabled.clone();
    BitSet done = done_.get(state);
    if (done != null) {
      result.andNot(done);
    }
    return result;
  }

  /** True if the given action has been executed from the given state.
   * @param state   A non-null state of the model.
   * @param action  The number of one of the actions of the model.
   * @return true if any transition (state, action, _) has been taken.
   */
  public boolean isDone(Object state, int action)
  {
    BitSet done = done_.get(state);
    if (done == null)
      return false;
    return done.get(action);
  }

  /**
   *  Returns a bitset of all the DONE bits for this state.
   *  Callers can mutate the returned BitSet.
   * @param state
   * @return A non-null BitSet.
   */
  public BitSet getDone(Object state)
  {
    BitSet result = done_.get(state);
    if (result == null) {
      return new BitSet();
    }
    else {
      return (BitSet) result.clone();
    }
  }

  /** Resets all the done and todo information.
   *  Immediately after calling this, isDone and isTodo will return false
   *  for every state and action.
   */
  public void clearDoneTodo()
  {
    if (! model_.isInitialState()) {
      model_.doReset("graphlistener");
    }
    Object curr = model_.getCurrentState();
    assert curr != null;
    done_ = new HashMap<Object,BitSet>();
    wasEnabled_ = new HashMap<Object,BitSet>();
    BitSet enabled = model_.enabledGuards();
    if (enabled.isEmpty())
      throw new FsmException("Initial state has no actions enabled.");
    wasEnabled_.put(curr, enabled);
  }

  /** Returns the graph of the FSM model.
   *  Note that the graph may be incomplete
   *  (call buildGraph to explore the graph thoroughly).
   */
  public InspectableGraph getGraph()
  {
    return fsmGraph_;
  }

  /**
   * Returns a map that maps each state of the model to
   * the corresponding vertex of the graph.
   * @return a map
   */
  public Map<Object,Vertex> getVertexMap()
  {
    return fsmVertex_;
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

  /** Starts to build the FSM graph by exploring the fsm object.
   *  This does a reset if the model is not already in the initial state.
   */
  @Override
  public void setModel(Model model)
  {
    super.setModel(model);
    clearDoneTodo();
    Object curr = model_.getCurrentState(); //the initial state
    // set up the initial state
    fsmGraph_ = new IncidenceListGraph();
    fsmVertex_ = new HashMap<Object,Vertex>();
    Vertex initial = fsmGraph_.insertVertex(curr);
    assert initial != null;
    printProgress(3, "buildgraph: start with vertex for initial state "+curr);
    fsmVertex_.put(curr, initial);
  }

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
   * @param state
   * @return A name that is suitable for printing in a .dot file.
   */
  public static String stateName(Object state)
  {
    String str = state.toString();
    if (str.matches("[a-zA-Z][a-zA-Z0-9_]*"))
      return str;
    else
      return "\"" + str.replaceAll("\"", "\\\"") + "\"";
  }

  /** Records a transition in the graph, if it is not already there.
   * @param action  The number of the action just taken
   * @param tr      A possibly new transition (and state).
   */
  @Override
  public void doneTransition(int action, Transition tr)
  {
    Object oldState = tr.getStartState();
    Vertex oldVertex = fsmVertex_.get(oldState);
    assert oldVertex != null;  // we must have already visited it.
    String actionName = tr.getAction();
    Object newState = tr.getEndState();
    assert newState == model_.getCurrentState();
    // see if this newState is an unknown one.
    Vertex newVertex = fsmVertex_.get(newState);
    if (newVertex == null) {
      // we have reached a new state, so add & analyze it.
      newVertex = fsmGraph_.insertVertex(newState);
      fsmVertex_.put(newState, newVertex);
      printProgress(3, "buildgraph: Added vertex for state "+newState);
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
      printProgress(3, "buildgraph: Added edge ("+oldState+","
          +actionName+","+newState+")");
    }

    // Now update done_ of the old state
    BitSet oldDone = done_.get(oldState);
    if (oldDone == null) {
      oldDone = new BitSet(); // all false
      done_.put(oldState, oldDone);
    }
    // now set the bit for the transition we've just done
    oldDone.set(action);

    // Now update wasEnabled_ of the new state
    BitSet nowTrue = model_.enabledGuards();
    BitSet wasTrue = wasEnabled_.get(newState);
    if (wasTrue == null) {
      wasTrue = nowTrue;
      wasEnabled_.put(newState, wasTrue);
    }
    else {
      wasTrue.or(nowTrue);
    }

    if (! complete_ && numTodo() == 0) {
      complete_ = true; // so we don't do this repeatedly
      // tell all the listeners about the graph
      printProgress(2, "completed graph, so calling setGraph");
      for (String name : model_.getListenerNames()) {
        ModelListener listen = model_.getListener(name);
        if (listen instanceof CoverageMetric) {
          ((CoverageMetric)listen).setGraph(fsmGraph_, fsmVertex_);
        }
      }
    }
  }
}
