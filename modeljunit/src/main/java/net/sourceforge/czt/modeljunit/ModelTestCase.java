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

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import junit.framework.TestCase;
import net.sourceforge.czt.jdsl.graph.api.Graph;
import net.sourceforge.czt.jdsl.graph.api.InspectableGraph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.jdsl.graph.ref.IncidenceListGraph;
import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;


/** Test a system, based on a finite state machine (FSM) model of that system.
 *  <p>
 *  TODO: separate out the MBT traversal algorithms, the model manager and 
 *  the coverage metrics into separate classes and make the methods 
 *  non-static.  Add an interface that FSMs must implement.
 *  We may be able to use the www.jdsl.org graph libraries to store
 *  and traverse the FSM.
 *  </p>
 *  <p>
 *  This class provides several methods that use model-based testing techniques
 *  to automatically generate test suites for a system under test (SUT) 
 *  from an FSM model of that system.  To use these methods, you write
 *  a special FSM class (see below) that models part of the behaviour of your
 *  SUT, then pass an instance of that class to one of the test generation
 *  methods (eg. @link{fsmRandomWalk}).  It will analyse the structure of
 *  your FSM model, then traverse various paths through your model to
 *  ensure that it is well tested.  Each methods of your FSM can change
 *  the state of the FSM, and can also perform some tests on the SUT
 *  and change its state.  So your FSM class is actually performing two roles:
 *  (1) defining a simplified FSM view of the behaviour of your SUT, and
 *  (2) mapping each transition of that FSM to a concrete test of your SUT.
 *  </p>
 *  
 *  <p>
 *  The FSM model is written as a Java class that has some private state 
 *  variables and some public methods that act as the transitions of the FSM.
 *  This FSM class must obey the following rules: 
 *  <ol>
 *    <li>It must have a <code>void init(boolean testing)</code> method.  
 *    This must reinitialise the FSM to its initial state, and if the testing
 *    argument is true it must also reset the underlying SUT to its initial state.
 *    (It may create a new SUT instance on each call to init, or just once).
 *    </li>
 *    
 *    <li>The toString() method must return a string representation of the
 *    current state of the FSM.  The current state of the FSM is usually
 *    an abstraction of the current state of the underlying SUT.
 *    </li>
 *    
 *    <li>It must have some <code>@Action void Meth()</code>
 *    methods.  These define all the transitions of the FSM.  Each of
 *    these Action methods may change the state of the FSM, and if the
 *    <code>testing</code> argument of the most recent <code>init(testing)</code>
 *    call was true, then these action methods should test some feature of the 
 *    underlying SUT and fail if errors are found.
 *    If the <code>testing</code> was false, then we are just traversing the FSM
 *    to determine its structure, so the SUT tests do not have to be run.
 *    
 *    <p>
 *    Some actions are not valid in all states, so you can add a
 *    <em>guard method</em> to say when that action is enabled.
 *    The guard method must have the same name as its action method
 *    but with "Guard" added at the end.  It must have no parameters and
 *    must return a boolean or float value (the latter are used for
 *    probabilistic testing). 
 *    The action method will only be called when its guard is true
 *    (or greater than 0.0F in the case of probabilistic guards). 
 *    So a typical action method with a guard will look like this:
 *    <pre>
 *      public boolean deleteGuard() { return ...; }
 *      public @action void delete()
 *      {
 *        ... perform the SUT test and check results ...
 *        fsmstate = ...new state of FSM...;
 *      }
 *    </pre>
 *    NOTE: If the SUT test part is expensive, then you can save the init(testing)
 *    flag and only do the SUT tests when that flag is true.
 *    </li>
 *  </ol>
 *  </p>
 *  
 *  <p>TODO:
 *    <ul>
 *      <li> record some coverage statistics and make them accessible via an API.</li>
 *      <li> add more test generation algorithms.</li>
 *    </ul>
 *  </p>
 */
public class ModelTestCase extends TestCase
{
  /** During random walk (including fsmBuildGraph), this is the
   *  probability of doing init() rather than choosing a random
   *  transition.  This must be non-zero in order to break out of
   *  cycles that do not have any path to the initial state.
   */
  public static final double INIT_PROBABILITY = 0.05;

  public static final int PATHLEN = 5;
  
  public ModelTestCase()
  {
      super();
  }

  public ModelTestCase( String testName )
  {
      super( testName );
  }

  /** This class defines the finite state machine model of the system under test.
   *  It is null until fsmLoad() has successfully loaded that class.
   */
  private static Class fsmClass = null;
  
  /** The name of the finite state machine model that is being tested. */
  private static String fsmName = null;

  /** The implementation under test (null means none yet). */
  //@invariant fsmModel != null ==> fsmClass != null;
  private static Object fsmModel = null;

  /** The init method of fsmClass. */
  //@invariant fsmInit == null <==> fsmClass == null;
  private static Method fsmInit = null;
  
  /** All the @Action methods of fsmClass. */
  //@invariant fsmActions == null <==> fsmClass == null;
  private static ArrayList<Method> fsmActions = null;

  /** All the guards of fsmClass. 
   *  These are in exactly the same order as fsmActions.
   *  A null entry means that that Action method has no guard. */
  //@invariant fsmGuards == null <==> fsmClass == null;
  private static ArrayList<Method> fsmGuards = null;

  /** The graph of all the states and transitions of this FSM. */
  //@invariant fsmGraph!=null ==> fsmClass!=null;
  protected static Graph fsmGraph;

  /** A map from fsm states to the corresponding vertex of fsmGraph. */
  //@invariant fsmVertex==null <==> fsmGraph==null;
  // invariant (obj,vertex) in fsmVertex <==> vertex.element()==obj;
  protected static Map<Object,Vertex> fsmVertex;

  /** Coverage listeners. */
  private static List<CoverageMetric> fsmCoverage = new ArrayList<CoverageMetric>();

  /** The current state of the implementation under test. */
  //@invariant fsmState == null <==> fsmModel == null;
  private static Object fsmState = null;
  
  /** Current test sequence */
  //@invariant fsmSequence == null <==> fsmModel == null;
  private static ArrayList<Transition> fsmSequence;

  /** An empty array of objects. */
  private static final Object[] fsmNoArgs = new Object[] {};
  
  /** Looks up an Action by name and returns its number.
   * @param name The name of an Action.
   * @return     The index within fsmActions/fsmGuards, else -1.
   */
  //@requires fsmClass != null;
  //@ensures -1 <= \result && \result < fsmActions.size();
  //@ensures \result >= 0 ==> name.equals(fsmActions.get(i).getName());
  protected static int fsmGetAction(String name)
  {
    for (int i=0; i < fsmActions.size(); i++) {
      if (name.equals(fsmActions.get(i).getName()))
        return i;
    }
    return -1;
  }
  
  /** Returns the FSM class that is the test model. */
  protected static Class fsmGetModelClass()
  {
	  return fsmClass;
  }
  
  /** Returns the name of the FSM class that is the test model. */
  protected static String fsmGetModelName()
  {
	  return fsmClass.getName();
  }

  /** Returns the graph of the FSM model.
   *  This will return null until after fsmBuildGraph has been called.
   */
  public static InspectableGraph fsmGetGraph()
  {
    return fsmGraph;
  }

  /** Maps a state to a vertex object of the FSM graph.
   *  This will return null until after fsmBuildGraph has been called.
   */
  public static Vertex fsmGetVertex(Object state)
  {
    if (fsmVertex == null)
      return null;
    else
      return fsmVertex.get(state);
  }

  /** Returns the model object that is begin tested. */
  protected static Object fsmGetModel()
  {
	  return fsmModel;
  }
  
  /** Returns the current state of the implementation under test. */
  protected static Object fsmGetState()
  {
    return fsmState;
  }
  
  /** Returns the name of the given Action. */
  //@requires fsmGetModelClass() != null;
  protected static Object fsmGetActionName(int index)
  {
	  return fsmActions.get(index).getName();
  }

  /** The total number of Actions. */
  //@requires fsmGetModel() != null;
  protected static int fsmGetNumActions()
  {
	  return fsmActions.size();
  }

  /** Print a warning, during analysis of the FSM class. 
   *  By default, this prints warnings to System.out.
   *  Subclasses can override this if they to do something different.
   */
  public static void printWarning(String msg)
  {
    System.out.println(msg);
  }

  /** Print progress messages, during FSM-based testing.
   *  This prints progress messages during the FSM analysis stages
   *  and during the actual testing.
   *  By default, this prints messages to System.out.
   *  Subclasses can override this if they to do something different.
   */
  public static void printProgress(String msg)
  {
    System.out.println(msg);
  }

  /** Reset all the coverage statistics.
   *  This can be called at any time, provided that an FSM
   *  model class has been loaded (that is, fsmGetClass() != null).
   */
  public static void fsmResetCoverageMetrics()
  {
    for (CoverageMetric cm : fsmCoverage)
      cm.reset();
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

  /** Iterate over all the coverage listeners */
  public List<CoverageMetric> getCoverageMetrics()
  {
    return fsmCoverage;
  }

  /** Loads the given class and finds its @Action methods.
   *  This method must be called before any fsm traversals are done.
   */
  protected static void fsmLoad(/*@non_null@*/ Class fsm)
  {
    if (fsmClass == fsm)
      return;  // done already
    fsmClass = null;
    fsmName = fsm.getName();
    fsmInit = null;
    fsmActions = new ArrayList<Method>();
    for (Method m : fsm.getMethods()) {
      if (m.getName().equals("init")
          && m.getParameterTypes().length == 1
          && m.getParameterTypes()[0].equals(boolean.class))
        fsmInit = m;
      else if (m.isAnnotationPresent(Action.class)) {
        Class[] paramTypes = m.getParameterTypes();
        if (paramTypes.length != 0)
          fail("ERROR: @Action method "+fsmName+"."+m.getName()
              +" must have no parameters."); 
        if (m.getReturnType() != void.class)
          printWarning("ERROR: @Action method "
              +fsmName+"."+m.getName()+" should be void.");
        printProgress("Adding method "+fsmName+"."+m.getName()
            +" to test suite as #"+fsmActions.size());
        fsmActions.add(m);
      }
    }
    int nActions = fsmActions.size();
    if (nActions == 0) {
      fail("ERROR: FSM model "+fsmName+" has no methods marked with @Action.");
    }
    // Now look for guards of the Action methods.
    fsmGuards = new ArrayList<Method>(nActions);
    for (Method m : fsmActions)
      fsmGuards.add(null);  // all guards are null by default
    for (Method m : fsm.getMethods()) {
      if (m.getName().endsWith("Guard")
          && m.getParameterTypes().length == 0) {
        String trName = m.getName().substring(0, m.getName().length()-5);
        int trPos = fsmGetAction(trName);
        if (trPos < 0)
          printWarning("Warning: "+fsmName+"."+m.getName()
              +" guard does not match any Action method.");
        else if (m.getReturnType() != boolean.class
              && m.getReturnType() != float.class) {
          printWarning("Warning: guard method "+fsmName+"."+m.getName()
              +" must return boolean or float.");
        }
        else {
          fsmGuards.add(trPos, m);
          printProgress("Adding guard "+fsmName+"."+m.getName());
        }
      }
    }
    if (fsmInit == null) {
      fail("ERROR: FSM model "+fsm.getClass()+" has no init(boolean) method.");
    }
    // get ready to record coverage statistics.
    fsmResetCoverageMetrics();
    // now set fsmClass, to show that it is a valid FSM class.
    fsmClass = fsm;
  }
  
  /** Builds the FSM graph with a default random seed.
   *  @see #fsmBuildGraph(Object, Random)
   */
  public static void fsmBuildGraph(Object fsm)
  {
    fsmBuildGraph(fsm, new Random(123456789L));
  }

  /** Builds the FSM graph by exploring the fsm object.
   *  After the graph is built, it calls the setModel method
   *  of all the coverage listeners.
   *  @param fsm  The model to explore.
   *  @param rand A random number generator to drive the exploration.
   */
  public static void fsmBuildGraph(Object fsm, Random rand)
  {
    int nTrans = 0; // number of transitions taken while building graph.
    int nInits = 0; // number of inits taken while building graph.
    fsmGraph = new IncidenceListGraph();
    fsmVertex = new HashMap<Object,Vertex>();
    // This records the (state,action) pairs that have not yet been explored.
    Map<Object,BitSet> todo = new HashMap<Object,BitSet>();
    // set up the initial state
    {
      fsmInit(fsm, false);
      nInits++;
      Vertex initial = fsmGraph.insertVertex(fsmState);
      printProgress("Buildgraph: Added vertex for initial state "+fsmState);
      fsmVertex.put(fsmState, initial);
      BitSet enabled = fsmEnabledActions();
      if (enabled.isEmpty())
        throw new FsmException("Initial state has no actions enabled.");
      todo.put(fsmState, enabled);
    }
    // Loop invariants: 
    //   fsmState is the current state we are exploring.
    //   todo does not contain any empty BitSets.
    //   for every transition (s0,action,s1) in the FSM, exactly one
    //     of the following is true:
    //       s0 has not yet been visited, or
    //       todo(s0) has a bit set for action, or
    //       (s0,action,s1) has been added to fsmGraph.
    //
    while ( ! todo.isEmpty()) {
      BitSet enabled = todo.get(fsmState);
      printProgress("  Buildgraph: todo("+fsmState+") = "+enabled);
      if (enabled == null) {
        // If this state has some enabled actions, then we might choose
        // one of them randomly using fsmDoRandomAction, or we might
        // do an init (with probability BUILD_INIT_PROBABILITY).
        // This means we break out of closed loops that cannot reach
        // the initial state after an average of 1.0/BUILD_INIT_PROBABILITY
        // transitions.
        // If there are no enabled actions, we MUST do the init.
        Object oldState = fsmState;
        int action = -2;  // -2 means we did not even try fsmDoRandomAction.
        if (rand.nextDouble() >= INIT_PROBABILITY)
          action = fsmDoRandomAction(rand); // try a normal action
        if (action >= 0) {
          nTrans++;
          printProgress("Buildgraph: Took random action ("+oldState+", "
              +action+" "+fsmActions.get(action).getName()+", "+fsmState+")");
        }
        else {
          fsmInit(fsm, false);
          nInits++;
          String msg = (action == -2) ? "Random init." : "Had to init.";
          printProgress("Buildgraph: "+msg+"  State is "+fsmState);
        }
      }
      else {
        int action = enabled.nextSetBit(0);
        assert action >= 0;  // our invariant says it should not be empty.
        enabled.clear(action); // mark this transition as done.
        if (enabled.isEmpty())
          todo.remove(fsmState); // mark this whole state as done.
        Object oldState = fsmState;
        Vertex oldVertex = fsmVertex.get(oldState);
        fsmDoAction(action);
        nTrans++;
        // see if this fsmState is a new one.
        Vertex newVertex = fsmVertex.get(fsmState);
        if (newVertex == null) {
          // we have reached a new state, so add & analyze it.
          newVertex = fsmGraph.insertVertex(fsmState);
          fsmVertex.put(fsmState, newVertex);
          printProgress("Buildgraph: Added vertex for state "+fsmState);
          enabled = fsmEnabledActions();
          if ( ! enabled.isEmpty())
            todo.put(fsmState, enabled);
        }
        String actionName = fsmActions.get(action).getName();
        fsmGraph.insertDirectedEdge(oldVertex, newVertex, actionName);
        printProgress("Buildgraph: Added edge ("+oldState+","
            +actionName+","+fsmState+")");
      }
    }
    for (CoverageMetric cm : fsmCoverage) {
      cm.setModel(fsmGraph, fsmVertex);
    }
    printProgress("Buildgraph: Model complete after "
        +nInits+" inits and "+nTrans+" transitions.");
  }

  /** Reinitialise the FSM to its initial state.
   *  This does the fsmLoad of fsm.class if it has not
   *  already been done.  It also calls the doneInit(testing)
   *  method of all the coverage listeners.
   *  
   *  @param fsm     The FSM model that is being tested.
   *  @param testing False means we are just exploring the graph, so the
   *                 fsm object could skip the actual tests if it wants.
   */
  public static void fsmInit(Object fsm, boolean testing)
  {
    try {
      fsmLoad(fsm.getClass());
      fsmModel = fsm;
      fsmInit.invoke(fsm, new Object[]{testing});
      if (fsmSequence == null)
        fsmSequence = new ArrayList<Transition>();
      fsmSequence.clear();
      fsmState = fsm.toString();
      for (CoverageMetric cm : fsmCoverage)
        cm.doneInit(testing);
    } catch (Exception ex) {
      fail("Error calling FSM init method: " + ex.getMessage());
    }
  }

  /** Is Action number 'index' enabled?
   *  Returns 0.0 if Action number 'index' is disabled,
   *  or a positive number if it is enabled.
   *  Missing guard methods return 1.0F, while boolean guard methods
   *  return 1.0F when true and 0.0F when false.
   * @param  fsm    The instance of the FSM that is being tested.
   * @param  index  Index into the fsmActions array.
   * @return        The `enabledness' of this Action.
   */
  public static float fsmEnabled(int index)
  {
    Method guard = fsmGuards.get(index);
    if (guard == null)
      return 1.0F; // missing guards are always true.
    Object result = null;
    try {
      result = guard.invoke(fsmModel, fsmNoArgs);
    }
    catch (Exception ex) {
      fail("Exception while calling guard "+guard.getName()+", "+ex);
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
  public static BitSet fsmEnabledActions()
  {
    BitSet enabled = new BitSet();
    for (int i=0; i < fsmActions.size(); i++) {
      if (fsmEnabled(i) > 0.0F)
        enabled.set(i);
    }
    return enabled;
  }

  /** Try to take the given Action from the current state.
   *  Returns true if the Action was taken, false if it was disabled.
   * @param  index  Index into the fsmTransitions array.
   * @return        True if taken, false if it is disabled.
   */
  protected static boolean fsmDoAction(int index)
  {
	  if (fsmEnabled(index) <= 0.0)
		  return false;
	  
	  Method m = fsmActions.get(index);
	  try {
		  m.invoke(fsmModel, fsmNoArgs);
	  }
	  catch (InvocationTargetException ex) {
        StringBuffer msg = new StringBuffer();
        msg.append("Error calling "+fsmGetModelName()+"."+m.getName()+"()"
          + " in state "+fsmState);
        for (int i=1; i<=PATHLEN && i<=fsmSequence.size(); i++) {
          msg.append("\n\tafter "
              +fsmSequence.get(fsmSequence.size()-i).toString());
        }
        if (PATHLEN < fsmSequence.size())
          msg.append("\n\t...");
        
        /* Here is an alternative which throws just the original exception.
         * However, this does not allow us to add the model path like above.
         
        if (ex.getCause() != null
            && ex.getCause() instanceof AssertionFailedError) {
          AssertionFailedError origEx = (AssertionFailedError) ex.getCause();
          throw origEx;
        }
        */
		throw new RuntimeException(msg.toString(), ex.getCause());
	  }
      catch (IllegalAccessException ex) {
        fail("Error in model.  Non-public actions? "+ex);
      }
      Object newState = fsmModel.toString();
      Transition done = new Transition(fsmState, m.getName(), newState);
      fsmSequence.add(done);
      fsmState = newState;
	  for (CoverageMetric cm : fsmCoverage)
        cm.doneTransition(done);
	  return true;
  }

  /** Take any randomly-chosen Action that is enabled.
   *  Returns the number of the Action taken, -1 if all are disabled.
   * @param rand  The Random number generator that controls the choice.
   * @return      The Action taken, or -1 if none are enabled.
   */
  protected static int fsmDoRandomAction(Random rand)
  {
    int nTrans = fsmGetNumActions();
    BitSet tried = new BitSet(nTrans);
    int index = rand.nextInt(nTrans);
    //System.out.println("random choice is "+index);
    while (tried.cardinality() < nTrans) {
      while (tried.get(index)) {
        index = rand.nextInt(nTrans);
        //System.out.println("random RETRY gives "+index);
      }
      tried.set(index); // we have tried this one.
      if (fsmDoAction(index)) {
        return index;
      }
      Method m = fsmActions.get(index);
    }
    return -1;
  }

  /** Calls fsmRandomWalk/3 with a fixed seed so that tests are repeatable. */
  //@requires 0 <= length;
  public static void fsmRandomWalk(/*@non_null@*/ Object fsm, int length)
  {
    fsmRandomWalk(fsm, length, new Random(123456789L));
  }


  /** Does a random walk through a finite state machine.
   *  It tests exactly 'length' transitions.
   *  If it has not finished testing, but gets into a state
   *  where there are no Actions enabled, then it will
   *  use the <code>init()</code> method of the FSM to start
   *  from the initial state again.
   *  <p>
   *  If you want to test a different path each time this
   *  is called, then pass <code>new Random()</code> as the
   *  third parameter.  If you want to test the same path
   *  each time (this makes the test results more predictable),
   *  then pass <code>new Random(<em>fixedSeed</em>)</code>.
   *  ({@link #fsmRandomWalk(Object, int) fsmRandomWalk(fsm,length)}
   *  does this for you). 
   *  
   * @param fsm    This object defines a finite state machine model of the SUT.
   * @param length The number of transitions to test.
   * @param rand   A random number generator to control the traversal.
   */
  //@requires 0 <= length;
  public static void fsmRandomWalk(
      /*@non_null@*/ Object fsm, 
      int length,
      /*@non_null@*/ Random rand)
  {
	int totalLength = 0;
    fsmInit(fsm, true);
    while (totalLength < length) {
      int taken = -1;
      double prob = rand.nextDouble();
      //System.out.println("random double is "+prob);
      if (prob >= INIT_PROBABILITY)
        taken = fsmDoRandomAction(rand);
      if (taken < 0)
    	fsmInit(fsm, true);
      else
    	totalLength++;
    }
  }
}
