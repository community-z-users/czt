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

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import junit.framework.Assert;
import net.sourceforge.czt.jdsl.graph.api.Edge;
import net.sourceforge.czt.jdsl.graph.api.EdgeIterator;
import net.sourceforge.czt.jdsl.graph.api.Graph;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.jdsl.graph.ref.IncidenceListGraph;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;
import net.sourceforge.czt.modeljunit.coverage.StateCoverage;


/** Test a system, based on a finite state machine (FSM) model of that system.
 *  <p>
 *  This class provides several methods that use model-based testing techniques
 *  to automatically generate test suites for a system under test (SUT)
 *  from an FSM model of that system.  To use these methods, you write a
 *  special FSM class (see {@link FsmModel}) that models part of the behaviour of
 *  your SUT, then pass an instance of that class to one of the test
 *  generation methods (eg. {@link #randomWalk(int)}).
 *  It will analyse the structure of your FSM model, then call various
 *  sequences of methods in your model to ensure that it is well tested.
 *  Each action method of your FSM can change the state of the FSM,
 *  and can also perform some tests on the SUT and change its state.
 *  So your FSM class is actually performing two roles:
 *  (1) Model: defining a simplified FSM view of the behaviour of your SUT;
 *  (2) Adaptor: mapping each transition of that FSM to a concrete test
 *      of your SUT.
 *  </p>
 *
 *  <p>TODO:
 *    <ul>
 *      <li> DONE: record coverage statistics and make them accessible via an API.</li>
 *      <li> DONE: separate out the MBT traversal algorithms, the model manager and
 *  the coverage metrics into separate classes and make the methods
 *  non-static.</li>
 *      <li> DONE: build the graph *during* the random walk traversal.</li>
 *      <li> DONE: when a test fails, throw a specific exception
 *           containing lots of model information.</li>
 *      <li> DONE: make reset probability and buildGraph timeout user-settable.</li>
 *      <li> add more test generation algorithms, such as greedy random.</li>
 *      <li> add support for Actions with parameters.</li>
 *      <li> extend doRandomAction(_) to take into account a state-based
 *           probability for each Action.  (i.e., Markov chains).
 *    </ul>
 *    Acknowledgements: This model-based testing library uses the
 *    JDSL (Java Data Structure Library, see http://www.jdsl.org) graph
 *    libraries to store and traverse the graph of the FSM.
 *  </p>
 *
 *  @deprecated Use one of the subclasses of Tester instead.
 */
public class ModelTestCase
{
  /** During random walk (including buildGraph), this is the
   *  default probability of doing reset() rather than choosing
   *  a random transition.
   */
  public static final double DEFAULT_RESET_PROBABILITY = 0.05;

  public static final long FIXEDSEED = 123456789L;

  /** Constructs an FSM model from the given FsmModel object.
   * @param model
   */
  public ModelTestCase(FsmModel model)
  {
    loadModelClass(model.getClass());
    fsmModel = model;
    doReset("Initial", true);
    startBuildGraph();
  }

  /** Controls how many progress messages will be printed.
   *  @see #setProgressVerbosity(int)
   */
  private int progressVerbosity = 0;

  /** Controls how much information will be printed when a test fails.
   *  @see #setFailureVerbosity(int)
   */
  private int failureVerbosity = 3;

  /** Number of failed tests. */
  private int failedTests = 0;

  /** The probability that doRandomAction does a reset. */
  private double resetProbability = DEFAULT_RESET_PROBABILITY;

  /** This class defines the finite state machine model of the system under test.
   *  It is null until fsmLoad() has successfully loaded that class.
   */
  private Class fsmClass = null;

  /** The name of the finite state machine model that is being tested. */
  private String fsmName = null;

  /** The implementation under test (null means none yet). */
  //@invariant fsmModel != null ==> fsmClass != null;
  private FsmModel fsmModel = null;

  /** All the @Action methods of fsmClass. */
  //@invariant fsmActions == null <==> fsmClass == null;
  private ArrayList<Method> fsmActions = null;

  /** All the guards of fsmClass.
   *  These are in exactly the same order as fsmActions.
   *  A null entry means that that Action method has no guard. */
  //@invariant fsmGuards == null <==> fsmClass == null;
  private ArrayList<Method> fsmGuards = null;

  /** The graph of all the states and transitions of this FSM.
   *  Here are several invariants of the graph structures:
   *  <ul>
   *    <li>fsmState is the current state we are exploring.</li>
   *    <li>fsmTodo does not contain any empty BitSets.</li>
   *    <li>fsmDone can contain empty BitSets and its domain is
   *        the same as the domain of fsmVertex.</li>
   *    <li>for every transition (s0,action,s1) in the FSM, exactly
   *    one of the following is true:
   *    <ol>
   *      <li>s0 has not yet been visited, or</li>
   *      <li>fsmTodo(s0) has a bit set for action, or</li>
   *      <li>(s0,action,s1) has been added to fsmGraph and
   *          fsmDone(s0) has a bit set for action.</li>
   *    <ol>
   *  </ul>
   */
  //@invariant fsmGraph!=null ==> fsmClass!=null;
  private Graph fsmGraph;

  /** A map from fsm states to the corresponding vertex of fsmGraph. */
  //@invariant fsmVertex==null <==> fsmGraph==null;
  // invariant (obj,vertex) in fsmVertex <==> vertex.element()==obj;
  private Map<Object,Vertex> fsmVertex;

  /** Records the (state,action) pairs that have been explored. */
  private Map<Object,BitSet> fsmDone;

  /** Records the (state,action) pairs that have not been explored. */
  private Map<Object,BitSet> fsmTodo;

  /** Coverage listeners. */
  private static List<CoverageMetric> fsmCoverage
    = new ArrayList<CoverageMetric>();

  /** The current state of the implementation under test. */
  //@invariant fsmState != null ==> fsmModel != null;
  private Object fsmState = null;

  /** The initial state of the implementation under test. */
  //@invariant fsmInitialState == null <==> fsmState == null;
  private Object fsmInitialState = null;

  /** Current test sequence */
  //@invariant fsmSequence == null <==> fsmModel == null;
  private ArrayList<Transition> fsmSequence;

  /** An empty array of objects. */
  private static final Object[] fsmNoArgs = new Object[] {};

  /** Looks up an Action by name and returns its number.
   * @param name The name of an Action.
   * @return     The index within fsmActions/fsmGuards, else -1.
   */
  //@requires fsmClass != null;
  //@ensures -1 <= \result && \result < fsmActions.size();
  //@ensures \result >= 0 ==> name.equals(fsmActions.get(i).getName());
  protected int fsmFindAction(String name)
  {
    for (int i=0; i < fsmActions.size(); i++) {
      if (name.equals(fsmActions.get(i).getName()))
        return i;
    }
    return -1;
  }

  /** Returns the number of test failures. */
  public int getFailedTests()
  {
    return failedTests;
  }

  /** The probability of spontaneously doing a reset rather than
   * a normal transition during random walks etc.
   * @return the reset probability
   */
  public double getResetProbability()
  {
    return resetProbability;
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
      resetProbability = prob;
    else
      throw new IllegalArgumentException("illegal reset probability: "+prob);
  }

  /** Says how many progress messages will be printed. */
  public int getVerbosity()
  {
    return progressVerbosity;
  }

  /** Sets the level of progress messages that will be printed
   *  as this class builds the FSM graph and generates tests.
   *  0 means no messages.  1 means statistical summaries only.
   *  2 means also show each transition taken.  3 means also
   *  show progress messages as the FSM graph is built.
   * @param verbosity  0..3
   */
  public void setVerbosity(int verbosity)
  {
    this.progressVerbosity = verbosity;
  }

  /** The amount of information printed when a test fails. */
  public int getFailureVerbosity()
  {
    return failureVerbosity;
  }

  /** Sets the amount of information printed when tests fail.
   *  0 means none.  1 means print a statistical summary of the
   *  number of failed tests.  2 means print a one line summary
   *  of each failed test.  3 means print more information about
   *  each failed test.
   * @param failureVerbosity 0..3
   */
  public void setFailureVerbosity(int failureVerbosity)
  {
    this.failureVerbosity = failureVerbosity;
  }

  /** Returns the FSM class that is the test model. */
  protected Class getModelClass()
  {
	  return fsmClass;
  }

  /** Returns the name of the FSM class that is the test model. */
  protected String getModelName()
  {
	  return fsmClass.getName();
  }

  /** Returns the graph of the FSM model.
   *  Note that the graph may be incomplete
   *  (call buildGraph to explore the graph thoroughly).
   */
  public InspectableGraph getGraph()
  {
    return fsmGraph;
  }

  /** Maps a state to a vertex object of the FSM graph.
   *  This may return null until after buildGraph has been called.
   */
  public Vertex getVertex(Object state)
  {
    if (fsmVertex == null)
      return null;
    else
      return fsmVertex.get(state);
  }

  /** Returns the model object that is begin tested. */
  protected Object getModel()
  {
	  return fsmModel;
  }

  /** Returns the current state of the implementation under test. */
  protected Object getCurrentState()
  {
    return fsmState;
  }

  /** Returns the name of the given Action. */
  //@requires fsmGetModelClass() != null;
  protected Object getActionName(int index)
  {
	  return fsmActions.get(index).getName();
  }

  /** The total number of Actions. */
  //@requires fsmGetModel() != null;
  protected int getNumActions()
  {
	  return fsmActions.size();
  }

  /** Print a warning, during analysis of the FSM class.
   *  By default, this prints warnings to System.out.
   *  Subclasses can override this if they to do something different.
   */
  public void printWarning(String msg)
  {
    System.out.println(msg);
  }

  /** Print progress messages, during FSM-based testing.
   *  This prints progress messages during the FSM analysis stages
   *  and during the actual testing.
   *  By default, this prints messages to System.out.
   *  Subclasses can override this if they want to do something different.
   * @param priority 1..3
   */
  public void printProgress(int priority, String msg)
  {
    if (priority <= progressVerbosity)
      System.out.println("ModelJUnit: "+msg);
  }

  /** Print failure messages, when a test/tests fail.
   *  By default, this prints messages to System.out.
   *  Subclasses can override this if they to do something different.
   * @param priority 1..3
   */
  public void printFailure(int priority, String msg)
  {
    if (priority <= failureVerbosity)
      System.out.println("FAILURE: "+msg);
  }

  /** Reset all the coverage statistics.
   *  This can be called at any time, provided that an FSM
   *  model class has been loaded (that is, fsmGetClass() != null).
   */
  public static void resetCoverageMetrics()
  {
    for (CoverageMetric cm : fsmCoverage)
      cm.clear();
  }

  /** Add a coverage listener. */
  public static void addCoverageMetric(CoverageMetric cover)
  {
    fsmCoverage.add(cover);
  }

  /** Remove a coverage listener. */
  public static boolean removeCoverageMetric(CoverageMetric cover)
  {
    return fsmCoverage.remove(cover);
  }

  /** Remove all coverage listeners. */
  public static void removeAllCoverageMetrics()
  {
    fsmCoverage.clear();
  }

  /** A list of all the current coverage listeners */
  public List<CoverageMetric> getCoverageMetrics()
  {
    return fsmCoverage;
  }

  /** Loads the given class and finds its @Action methods.
   *  This method must be called before any fsm traversals are done.
   */
  protected void loadModelClass(/*@non_null@*/ Class fsm)
  {
    if (fsmClass == fsm)
      return;  // done already
    fsmClass = null;
    fsmName = fsm.getName();
    printProgress(3, "loading model class: "+fsmName);
    fsmActions = new ArrayList<Method>();
    for (Method m : fsm.getMethods()) {
      if (m.isAnnotationPresent(Action.class)) {
        Class[] paramTypes = m.getParameterTypes();
        if (paramTypes.length != 0)
          Assert.fail("ERROR: @Action method "+fsmName+"."+m.getName()
              +" must have no parameters.");
        if (m.getReturnType() != void.class)
          printWarning("ERROR: @Action method "
              +fsmName+"."+m.getName()+" should be void.");
        // insert m into fsmActions_ in alphabetical order.
        int pos=0;
        while (pos < fsmActions.size()) {
          if (fsmActions.get(pos).getName().compareTo(m.getName()) > 0) {
            break;
          }
          pos++;
        }
        fsmActions.add(pos, m);
        printProgress(3, "added method "+fsmName+"."+m.getName()
            +" to model as action#"+pos);
      }
    }
    int nActions = fsmActions.size();
    if (nActions == 0) {
      Assert.fail("ERROR: FSM model "+fsmName+" has no methods annotated with @Action.");
    }
    // Now look for guards of the Action methods.
    fsmGuards = new ArrayList<Method>(nActions);
    for (Method m : fsmActions)
      fsmGuards.add(null);  // all guards are null by default
    for (Method m : fsm.getMethods()) {
      if (m.getName().endsWith("Guard")
          && m.getParameterTypes().length == 0) {
        String trName = m.getName().substring(0, m.getName().length()-5);
        int trPos = fsmFindAction(trName);
        if (trPos < 0)
          printWarning("Warning: "+fsmName+"."+m.getName()
              +" guard does not match any Action method.");
        else if (m.getReturnType() != boolean.class
              && m.getReturnType() != float.class) {
          printWarning("Warning: guard method "+fsmName+"."+m.getName()
              +" must return boolean or float.");
        }
        else {
          fsmGuards.set(trPos, m);
          printProgress(3, "set guard["+trPos+"] := "+fsmName+"."+m.getName());
        }
      }
    }
    printProgress(3, "finished loading model class: "+fsmName);
    // get ready to record coverage statistics.
    resetCoverageMetrics();
    // now set fsmClass, to show that it is a valid FSM class.
    fsmClass = fsm;
  }

  /** Starts to build the FSM graph by exploring the fsm object.
   *  This assumes that the current fsmState is the initial state.
   *  That is, a reset has just been done.
   */
  protected void startBuildGraph()
  {
    assert fsmState != null;
    fsmGraph = new IncidenceListGraph();
    fsmVertex = new HashMap<Object,Vertex>();
    fsmDone = new HashMap<Object,BitSet>();
    fsmTodo = new HashMap<Object,BitSet>();
    // set up the initial state
    Vertex initial = fsmGraph.insertVertex(fsmState);
    assert initial != null;
    printProgress(3, "buildgraph: start with vertex for initial state "+fsmState);
    fsmVertex.put(fsmState, initial);
    fsmDone.put(fsmState, new BitSet());
    BitSet enabled = currentEnabledActions();
    if (enabled.isEmpty())
      throw new FsmException("Initial state has no actions enabled.");
    fsmTodo.put(fsmState, enabled);
  }

  /** Records a transition in the graph, if it is not already there.
   *  This internal method should be called by doAction, so that
   *  it can analyze/record every transition.  It is quite like
   *  a coverage listener, but I decided to make it more built-in
   *  because the graph is so fundamental to model-based testing.
   * @param tr  A possibly new transition (and state).
   */
  protected void continueBuildGraph(Transition tr, int action)
  {
    Object oldState = tr.getStartState();
    Vertex oldVertex = fsmVertex.get(oldState);
    assert oldVertex != null;  // we must have already visited it.
    String actionName = tr.getAction();
    Object newState = tr.getEndState();
    assert newState == fsmState;  // we should still be inside doAction.
    BitSet enabled = currentEnabledActions();
    // see if this newState is an unknown one.
    Vertex newVertex = fsmVertex.get(newState);
    if (newVertex == null) {
      // we have reached a new state, so add & analyze it.
      newVertex = fsmGraph.insertVertex(newState);
      fsmVertex.put(newState, newVertex);
      fsmDone.put(newState, new BitSet());
      printProgress(3, "buildgraph: Added vertex for state "+newState);
      if ( ! enabled.isEmpty())
        fsmTodo.put(newState, enabled);
    }
    else {
      // see if we need to add some bits to fsmTodo.
      enabled.andNot(fsmDone.get(newState));
      if ( ! enabled.isEmpty()) {
        BitSet oldTodo = fsmTodo.get(newState);
        if (oldTodo == null)
          fsmTodo.put(newState, enabled);
        else
          oldTodo.or(enabled);
      }
    }
    // see if fsmGraph already contains this edge.
    boolean present = false;
    EdgeIterator edges = fsmGraph.connectingEdges(oldVertex, newVertex);
    while (edges.hasNext()) {
      Edge edge = edges.nextEdge();
      if (edge.element().equals(actionName)
          && fsmGraph.origin(edge) == oldVertex
          && fsmGraph.destination(edge) == newVertex) {
        present = true;
        break;
      }
    }
    if ( ! present) {
      fsmGraph.insertDirectedEdge(oldVertex, newVertex, actionName);
      fsmDone.get(oldState).set(action);
      printProgress(3, "buildgraph: Added edge ("+oldState+","
          +actionName+","+newState+")");

      // See if we can reduce the fsmTodo flags of oldState
      BitSet bset = fsmTodo.get(oldState);
      if (bset != null) {
        bset.clear(action);
        if (bset.isEmpty())
          fsmTodo.remove(oldState);
      }
    }
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
  public boolean buildGraph(Random rand, int maxTransitions)
  {
    int maxLen = maxTransitions;
    while (fsmTodo.size() > 0 && maxLen > 0) {
      maxLen--;
      doRandomActionOrReset(rand, false);
    }
    for (CoverageMetric cm : fsmCoverage) {
      cm.setGraph(fsmGraph, fsmVertex);
    }
    if (fsmTodo.size() == 0) {
      // we seem to have explored all paths
      printProgress(1, "FSM has "+this.fsmGraph.numVertices()
          +" states and "+this.fsmGraph.numEdges()+" transitions.");
      return true;
    }
    else {
        printProgress(1, "BuildGraph still has " + fsmTodo.size()
            + " unexplored paths after " + maxTransitions
            + " transitions.  FSM too big?");
        return false;
    }
  }

  /** Equivalent to buildGraph(new Random(FIXEDSEED), 10000). */
  public boolean buildGraph(Random rand)
  {
    return buildGraph(new Random(FIXEDSEED), 10000);
  }

  /** Equivalent to buildGraph(new Random(FIXEDSEED)). */
  public boolean buildGraph()
  {
    return buildGraph(new Random(FIXEDSEED));
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
    if (fsmGraph == null)
      throw new IllegalStateException("Graph not built yet.  Call buildGraph.");
    PrintWriter output = new PrintWriter(filename);
    String shortName = getModelName();
    shortName = shortName.substring(shortName.lastIndexOf('.')+1);
    output.println("digraph "+shortName);
    output.println("{");
    EdgeIterator edges = fsmGraph.edges();
    while (edges.hasNext()) {
      Edge e = edges.nextEdge();
      Object origin = fsmGraph.origin(e).element();
      Object dest = fsmGraph.destination(e).element();
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
   * @return A printable state name
   */
  public static String stateName(Object state)
  {
    String str = state.toString();
    if (str.matches("[a-zA-Z][a-zA-Z0-9_]*"))
      return str;
    else
      return "\"" + str.replaceAll("\"", "\\\"") + "\"";
  }

  /** Reset the FSM to its initial state.
   *  This is equivalent to doReset("User",testing),
   *  because it corresponds to a user-requested reset.
   * @param testing
   */
  public void doReset(boolean testing)
  {
    doReset("User", testing);
  }

  /** Reset the FSM to its initial state.
   *  This does the fsmLoad of fsm.class if it has not
   *  already been done.  It also calls the doneReset(testing)
   *  method of all the coverage listeners.
   * @param reason  Why the reset was performed (an adjective).
   * @param testing False means we are just exploring the graph, so the
   *                 fsm object could skip the actual tests if it wants.
   */
  protected void doReset(String reason, boolean testing)
  {
    if (fsmSequence == null)
      fsmSequence = new ArrayList<Transition>();
    else
    {
      this.printProgress(1, "tested "+fsmSequence.size()+" transitions.  "
          +reason+" reset from state "+fsmState);
    }
    try {
      this.printProgress(2, "reset("+testing+")");
      fsmModel.reset(testing);
      fsmSequence.clear();
      fsmState = fsmModel.getState();
      Assert.assertNotNull("Model Error: getState() must be non-null", fsmState);
      if (fsmInitialState == null)
        fsmInitialState = fsmState;
      else {
        Assert.assertEquals("Model error: reset did not return to the initial state",
            fsmInitialState, fsmState);
      }
      for (CoverageMetric cm : fsmCoverage)
        cm.doneReset(reason, testing);
    } catch (Exception ex) {
      throw new RuntimeException("Error calling FSM reset method.", ex);
    }
  }

  /** Is Action number 'index' enabled?
   *  Returns 0.0 if Action number 'index' is disabled,
   *  or a positive number if it is enabled.
   *  Missing guard methods return 1.0F, while boolean guard methods
   *  return 1.0F when true and 0.0F when false.
   * @param  index  Index into the fsmActions array.
   * @return        The `enabledness' of this Action.
   */
  public float enabled(int index)
  {
    Method guard = fsmGuards.get(index);
    if (guard == null)
      return 1.0F; // missing guards are always true.
    Object result = null;
    try {
      result = guard.invoke(fsmModel, fsmNoArgs);
    }
    catch (Exception ex) {
      Assert.fail("Exception while calling guard "+guard.getName()+", "+ex);
    }
    if (guard.getReturnType() == boolean.class) {
      if ( ((Boolean)result).booleanValue() )
        return 1.0F;
      else
        return 0.0F;
    }
    return ((Float)result).floatValue();
  }

  /** Return the bitset of all actions that are enabled
   *  in the current state. */
  public BitSet currentEnabledActions()
  {
    BitSet enabled = new BitSet();
    for (int i=0; i < fsmActions.size(); i++) {
      if (enabled(i) > 0.0F)
        enabled.set(i);
    }
    return enabled;
  }

  /** Try to take the given Action from the current state.
   *  Returns true if the Action was taken, false if it was disabled.
   * @param  index  Index into the fsmTransitions array.
   * @return        True if taken, false if it is disabled.
   */
  protected boolean doAction(int index)
  {
    if (enabled(index) <= 0.0)
      return false;

    Method m = fsmActions.get(index);
    try {
      this.printProgress(2, "testing action "+m.getName()+ " from state "+fsmState);
      m.invoke(fsmModel, fsmNoArgs);
    }
    catch (InvocationTargetException ex) {
      String failmsg = "failure in action "+m.getName()
      +" from state "+this.fsmState+" due to "+ex.getCause();
      // TODO: find out why setting the cause here is not enough
      //     to make the cause's stack trace appear in the junit output.
      TestFailureException failure =
        new TestFailureException(failmsg, ex.getCause());
      failure.setActionName(m.getName());
      failure.setModel(this.fsmModel);
      failure.setModelName(this.getModelName());
      failure.setSequence(this.fsmSequence);
      failure.setState(this.fsmState);

      /* Here is an alternative which throws just the original exception.
       * However, this does not allow us to add the model path like above.

        if (ex.getCause() != null
            && ex.getCause() instanceof AssertionFailedError) {
          AssertionFailedError origEx = (AssertionFailedError) ex.getCause();
          throw origEx;
        }
       */
      failedTests++;
      printFailure(2, failmsg);
      if (3 <= failureVerbosity && this.fsmSequence != null) {
        // print the sequence in reverse order, like a stacktrace
        for (int i=this.fsmSequence.size()-1; i>=0; i--)
          printFailure(3, "  after "+this.fsmSequence.get(i));
        printFailure(3, "  after reset.");
      }
      throw failure;
    }
    catch (IllegalAccessException ex) {
      Assert.fail("Model Error: Non-public actions? "+ex);
    }
    Object newState = fsmModel.getState();
    Transition done = new Transition(fsmState, m.getName(), newState);
    fsmSequence.add(done);
    fsmState = newState;
    Assert.assertNotNull("Model Error: getState() must be non-null", fsmState);
    continueBuildGraph(done, index);
    for (CoverageMetric cm : fsmCoverage)
      cm.doneTransition(index, done);
    return true;
  }

  /** Take any randomly-chosen Action that is enabled.
   *  Returns the number of the Action taken, -1 if all are disabled.
   * @param rand  The Random number generator that controls the choice.
   * @return      The Action taken, or -1 if none are enabled.
   */
  protected int doRandomAction(Random rand)
  {
    int nTrans = getNumActions();
    BitSet tried = new BitSet(nTrans);
    int index = rand.nextInt(nTrans);
    //System.out.println("random choice is "+index+" out of "+nTrans);
    while (tried.cardinality() < nTrans) {
      while (tried.get(index)) {
        index = rand.nextInt(nTrans);
        //System.out.println("random RETRY gives "+index);
      }
      tried.set(index); // mark this one as having been tried.
      if (doAction(index)) {
        return index;
      }
    }
    return -1;
  }

  /** Randomly take an enabled transition, or do a reset
   * with a certain probability (see {@link #getResetProbability()}).
   *
   * @param rand The Random number generator that controls the choice.
   * @return   The number of the transition taken, or -1 for a reset.
   */
  public int doRandomActionOrReset(Random rand, boolean testing)
  {
    int taken = -1;
    double prob = rand.nextDouble();
    if (prob < resetProbability)
      doReset("Random", testing);
    else
    {
      taken = doRandomAction(rand);
      if (taken < 0)
        doReset("Forced", testing);
    }
    return taken;
  }

  /* Greedy random code
          int action = enabled.nextSetBit(0);
          assert action >= 0;  // our invariant says it should not be empty.
          enabled.clear(action); // mark this transition as done.
          if (enabled.isEmpty())
            fsmTodo.remove(fsmState); // mark this whole state as done.
          Object oldState = fsmState;
          Vertex oldVertex = fsmVertex.get(oldState);
          doAction(action);
  */

  /** Calls fsmRandomWalk/3 with FIXEDSEED so that tests are repeatable. */
  //@requires 0 <= length;
  public void randomWalk(int length)
  {
    randomWalk(length, new Random(FIXEDSEED));
  }

  /** Does a random walk through a finite state machine.
   *  It tests exactly 'length' transitions.
   *  If it has not finished testing, but gets into a state
   *  where there are no Actions enabled, then it will
   *  use the <code>reset()</code> method of the FSM to start
   *  from the initial state again.
   *  <p>
   *  If you want to test a different path each time this
   *  is called, then pass <code>new Random()</code> as the
   *  third parameter.  If you want to test the same path
   *  each time (this makes the test results more predictable),
   *  then pass <code>new Random(<em>fixedSeed</em>)</code>.
   *  ({@link #randomWalk(int) fsmRandomWalk(fsm,length)}
   *  does this for you).
   * @param length The number of transitions to test.
   * @param rand   A random number generator to control the traversal.
   */
  //@requires 0 <= length;
  public void randomWalk(int length,
  /*@non_null@*/Random rand)
  {
    int totalLength = 0;
    doReset("Initial", true);
    while (totalLength < length) {
      int taken = doRandomActionOrReset(rand, true);
      if (taken >= 0)
        totalLength++;
    }
    this.printProgress(1, "finished randomWalk of " + length + " transitions.");
    if (failedTests > 0)
      printFailure(1, "" + failedTests + " tests failed.");
  }

  protected int doGreedyRandomAction(Random rand)
  {
    // System.out.println("Currently in state: " + fsmState);
    /*
     BitSet of the actions that need to be done for the current state

     True, if action has not been done and is enabled
     False, Otherwise

     Null, if terminal state or state has no more unvisted transitions
     Non-Null, otherwise
     */
    BitSet toDo = fsmTodo.get(fsmState);
    /*
     BitSet of the actions have been done for the current state

     True, if action has been done
     False, Otherwise

     Null, if terminal state or state has not been visited
     Non-Null, otherwise
     */
    BitSet done = fsmDone.get(fsmState);
    // Indexes of the actions that need to be done
    ArrayList<Integer> indexToDo = new ArrayList<Integer>();

    // If terminal state we must force a reset so return -1
    if (toDo == null && done == null)
      return -1;
    else if (toDo == null && done != null) {
      // If all actions of the state have been done just choose one randomly
      return doRandomAction(rand);
    }

    // System.out.println("todo cardinality: " + toDo.cardinality());

    if (toDo.cardinality() == 0) {
      // If all actions of the state have been done just choose one randomly
      return doRandomAction(rand);
    }
    else if (toDo.cardinality() == 1) {
      // Get the index of the only set bit in the toDo Bitset
      int index = toDo.nextSetBit(0);
      if (doAction(index)) {
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
      int index = rand.nextInt(indexToDo.size());
      // System.out.println("index: " + index);
      if (doAction(indexToDo.get(index))) {
        // If action is done return the action that was done
        return indexToDo.get(index);
      }
    }
    return -1;
  }

  public int doGreedyRandomActionOrReset(Random rand, boolean testing)
  {
    int taken = -1;
    double prob = rand.nextDouble();
    if (prob < resetProbability)
      doReset("Random", testing);
    else {
      taken = doGreedyRandomAction(rand);
      if (taken < 0)
        doReset("Forced", testing);
    }
    return taken;
  }

  public void greedyRandomWalk(int length)
  {
    greedyRandomWalk(length, new Random(FIXEDSEED));
  }

  public void greedyRandomWalk(int length, Random rand)
  {
    int totalLength = 0;
    doReset("Initial", true);
    while (totalLength < length) {
      int taken = doGreedyRandomActionOrReset(rand, true);
      if (taken >= 0)
        totalLength++;
    }
    this.printProgress(1, "finished greedyRandomWalk of " + length
        + " transitions.");
    if (failedTests > 0)
      printFailure(1, "" + failedTests + " tests failed.");
  }

  /** Same as allRoundTrips(length), but uses a fixed seed for the
   *  random number generator.  This ensures repeatability.
   *  That is, the test results will be deterministic (if the SUT is).
   *
   * @param length  The number of test steps to do.
   */
  public void allRoundTrips(int length)
  {
    allRoundTrips(length, new Random(FIXEDSEED));
  }

  /** Uses a greedy random walk to try and test all loops in the model.
   *
   * @param length  The number of test steps to do.
   * @param rand    The random number generator used to choose paths.
   */
  public void allRoundTrips(int length, Random rand)
  {
    CoverageMetric state = new StateCoverage();
    this.addCoverageMetric(state);
    int totalLength = 0;
    doReset("Initial", true);
    while (totalLength < length) {
      int taken = doGreedyRandomActionOrReset(rand, true);
      if (taken < 0) {
        System.out.println("reset state coverage");
        state.clear();
      }
      else {
        totalLength++;
        if (state.getDetails().get(getCurrentState()) > 1) {
          doReset("found loop", true);
          state.clear();
        }
      }
    }
    this.printProgress(1, "finished allRoundTrips of " + length
        + " transitions.");
    if (failedTests > 0)
      printFailure(1, "" + failedTests + " tests failed.");
    this.removeCoverageMetric(state);
  }
}
