package net.sourceforge.czt.modeljunit;

import junit.framework.TestCase;
import java.lang.reflect.*;
import java.util.*;


/** Test a system, based on a finite state machine (FSM) model of that system.
 *  <p>
 *  TODO: separate out the MBT traversal algorithms, the model manager and 
 *  the coverage metrics into separate classes and make the methods 
 *  non-static. In fact, the coverage metric objects should be listeners
 *  attached to the model manager.  We may be able to use the
 *  www.jdsl.org graph libraries to store and traverse the FSM.
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
 *    <li>It must have some <code>@transition void Meth()</code>
 *    methods.  These define the transitions of the FSM.  Each of these
 *    transition methods may change the state of the FSM, and if the
 *    <code>testing</code> argument of the most recent <code>init(testing)</code>
 *    call was true, then these transitions should test some feature of the 
 *    underlying SUT and fail if errors are found.
 *    If the <code>testing</code> was false, then we are just traversing the FSM
 *    to determine its structure, so the SUT tests do not have to be run.
 *    
 *    <p>
 *    Some transitions are not valid in all states, so you can add a
 *    <em>guard method</em> to say when a transition is enabled.
 *    The guard method must have the same name as its transition method
 *    but with "Guard" added at the end.  It must have no parameters and
 *    must return a boolean or float value (the latter are used for
 *    probabilistic testing). 
 *    The transition method will only be called when its guard is true
 *    (or greater than 0.0F in the case of probabilistic guards). 
 *    So a typical transition method with a guard will look like this:
 *    <pre>
 *      public boolean deleteGuard() { return ...; }
 *      public @transition void delete()
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
 *      <li> better reporting of failed tests.</li>
 *      <li> record some coverage statistics and make them accessible via an API.</li>
 *      <li> add more test generation algorithms.</li>
 *    </ul>
 *  </p>
 */
public class ModelTestCase extends TestCase
{
  public ModelTestCase()
  {
      super();
  }

  public ModelTestCase( String testName )
  {
      super( testName );
  }

  /** This class defines the finite state machine model of the system under test.
   *  It is null until fsmInit() has successfully loaded that class.
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
  
  /** All the @transition methods of fsmClass. */
  //@invariant fsmTransitions == null <==> fsmClass == null;
  private static ArrayList<Method> fsmTransitions = null;

  /** All the guards of fsmClass. 
   *  These are in exactly the same order as fmsTransitions.
   *  A null entry means that that transition methods has no guard. */
  //@invariant fsmGuards == null <==> fsmClass == null;
  private static ArrayList<Method> fsmGuards = null;

  /** Statistics about the coverage of transitions. */
  //@invariant fsmTransitionCoverage == null <==> fsmModel == null;
  private static int[] fsmTransitionCoverage = null;
  
  /** Current test sequence */
  //@invariant fsmSequence == null <==> fsmModel == null;
  private static ArrayList<Integer> fsm;

  /** An empty array of objects. */
  private static final Object[] fsmNoArgs = new Object[] {};
  
  /** Looks up a transition by name.
   * @param name The name of a transition.
   * @return     The index within fsmTransitions/fsmGuards, else -1.
   */
  //@requires fsmClass != null;
  //@ensures -1 <= \result && \result < fsmTransitions.size();
  //@ensures \result >= 0 ==> name.equals(fsmTransitions.get(i).getName());
  protected static int fsmGetTransition(String name)
  {
    for (int i=0; i < fsmTransitions.size(); i++) {
      if (name.equals(fsmTransitions.get(i).getName()))
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
  
  /** Returns the name of the FSM class that is the test model. */
  protected static Object fsmGetModel()
  {
	  return fsmModel;
  }
  
  /** Returns the name of the given transition. */
  //@requires fsmGetModelClass() != null;
  protected static Object fsmGetTransitionName(int index)
  {
	  return fsmTransitions.get(index).getName();
  }

  /** The total number of transitions. */
  //@requires fsmGetModel() != null;
  protected static int fsmGetNumTransitions()
  {
	  return fsmTransitions.size();
  }

  /** The number of transitions covered since last fsmResetStatistics. */
  //@requires fsmGetModel() != null;
  protected static int fsmGetNumTransitionsCovered()
  {
	  int covered = 0;
	  for (int i=fsmGetNumTransitions()-1; i>=0; i--)
		  if (fsmTransitionCoverage[i] > 0)
			  covered++;
	  return covered;
  }

  /** Print a warning, during analysis of the FSM class. 
   *  By default, this prints warnings to System.err.
   *  Subclasses can override this if they to do something different.
   */
  public static void printWarning(String msg)
  {
    System.err.println(msg);
  }

  /** Print progress messages, during FSM-based testing.
   *  This prints progress messages during the FSM analysis stages
   *  and during the actual testing.
   *  By default, this prints messages to System.err.
   *  Subclasses can override this if they to do something different.
   */
  public static void printProgress(String msg)
  {
    System.err.println(msg);
  }
  
  /** Loads the given class and finds its @transition methods.
   *  This method must be called before any fsm traversals are done.
   */
  protected static void fsmLoad(/*@non_null@*/ Class fsm)
  {
    if (fsmClass == fsm)
      return;  // done already
    fsmClass = null;
    fsmName = fsm.getName();
    fsmInit = null;
    fsmTransitions = new ArrayList<Method>();
    for (Method m : fsm.getMethods()) {
      if (m.getName().equals("init")
          && m.getParameterTypes().length == 1
          && m.getParameterTypes()[0].equals(boolean.class))
        fsmInit = m;
      else if (m.isAnnotationPresent(transition.class)) {
        Class[] paramTypes = m.getParameterTypes();
        if (paramTypes.length != 0)
          fail("ERROR: @transition method "+fsmName+"."+m.getName()
              +" must have no parameters."); 
        if (m.getReturnType() != void.class)
          printWarning("ERROR: @transition method "
              +fsmName+"."+m.getName()+" should be void.");
        printProgress("Adding method "+fsmName+"."+m.getName()
            +" to test suite");
        fsmTransitions.add(m);
      }
    }
    int nTransitions = fsmTransitions.size();
    if (nTransitions == 0) {
      fail("ERROR: FSM model "+fsmName+" has no methods marked with @transition.");
    }
    // Now look for guards of the transition methods.
    fsmGuards = new ArrayList<Method>(nTransitions);
    for (Method m : fsmTransitions)
      fsmGuards.add(null);  // all guards are null by default
    for (Method m : fsm.getMethods()) {
      if (m.getName().endsWith("Guard")
          && m.getParameterTypes().length == 0) {
        String trName = m.getName().substring(0, m.getName().length()-5);
        int trPos = fsmGetTransition(trName);
        if (trPos < 0)
          printWarning("Warning: "+fsmName+"."+m.getName()
              +" guard does not match any transition method.");
        else if (m.getReturnType() != boolean.class
              && m.getReturnType() != float.class) {
          printWarning("Warning: guard method "+fsmName+"."+m.getName()
              +" must return boolean or float.");
        }
        else {
          fsmGuards.add(trPos, m);
          printProgress("Adding guard "+fsmName+"."+m.getName()
              +" to test suite");
        }
      }
    }
    if (fsmInit == null) {
      fail("ERROR: FSM model "+fsm.getClass()+" has no init(boolean) method.");
    }
    // get ready to record coverage statistics.
    fsmResetCoverage();
    // now set fsmClass, to show that it is a valid FSM class.
    fsmClass = fsm;
  }

  /** Reset all the coverage statistics.
   *  This can be called at any time, provided that an FSM
   *  model class has been loaded (that is, fsmGetClass() != null).
   */
  public static void fsmResetCoverage()
  {
	 fsmTransitionCoverage = new int[fsmTransitions.size()];
  }

  /** Reinitialise the FSM to its initial state.
   *  This also does the fsmLoad of fsm.class if it has not
   *  already been done.
   */
  public static void fsmInit(Object fsm, boolean testing)
  {
	  try {
	    fsmLoad(fsm.getClass());
	    fsmModel = fsm;
	    fsmInit.invoke(fsm, new Object[] {testing});
	  }
	  catch (Exception ex) {
		  fail("Error calling FSM init method: " + ex.getMessage());
	  }
  }

  /** Is transition number 'index' enabled?
   *  Returns 0.0 if transition number 'index' is disabled,
   *  or a positive number if it is enabled.
   *  Missing guard methods return 1.0F, while boolean guard methods
   *  return 1.0F when true and 0.0F when false.
   * @param  fsm    The instance of the FSM that is being tested.
   * @param  index  Index into the fsmTransitions array.
   * @return        The `enabledness' of this transition.
   */
  protected static float fsmEnabled(int index)
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
  
  /** Take the given transition.
   *  Returns true if the transition was taken, false if it was disabled.
   * @param  index  Index into the fsmTransitions array.
   * @return        True if taken, false if it is disabled.
   */
  protected static boolean fsmTransition(int index)
  {
	  if (fsmEnabled(index) <= 0.0)
		  return false;
	  
	  Method m = fsmTransitions.get(index);
	  try {
		  m.invoke(fsmModel, fsmNoArgs);
	  }
	  catch (Exception ex) {
		  fail("Error calling "+fsmGetModelName()+"."
				  +m.getName()+"(): "+ex.getMessage());
	  }
	  fsmTransitionCoverage[index]++;
	  return true;
  }

  /** Take any random enabled transition.
   *  Returns true if the transition was taken, false if it was disabled.
   * @param rand  The Random number generator that controls the choice.
   * @return      The transition taken, or -1 if none are enabled.
   */
  protected static int fsmRandomTransition(Random rand)
  {
	int nTrans = fsmGetNumTransitions();
	BitSet tried = new BitSet(nTrans);
	printProgress("STARTING SEARCH FOR TRANSITION");
	int index = rand.nextInt(nTrans);
	while (tried.cardinality() < nTrans) {
	  while (tried.get(index))
		index = rand.nextInt(nTrans);
	  printProgress("  Trying "+index);
	  tried.set(index); // we have tried this one.
	  if (fsmTransition(index)) {
		printProgress("  TOOK TRANSITION "+index+": "+fsmGetTransitionName(index));
		return index;
	  }
	  printProgress("  (disabled) "+index);
	  Method m = fsmTransitions.get(index);
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
   *  where there are no transitions enabled, then it will
   *  use the <code>init()</code> method of the FSM to start
   *  from the initial state again.
   *  <p>
   *  If you want to test a different path each time this
   *  is called, then pass <code>new Random()</code> as the
   *  third parameter.  If you want to test the same path
   *  each time (this makes the test results more predictable),
   *  then pass <code>new Random(<em>fixedSeed</em>)</code>.
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
      int taken = fsmRandomTransition(rand);
      if (taken == -1)
    	fsmInit(fsm, true);
      else
    	totalLength++;
    }
    int tested = fsmGetNumTransitionsCovered();
    int nTrans = fsmGetNumTransitions();
    double percent = 100.0 * (double) tested / (double) nTrans;
    printProgress("RandomWalk testing of "+fsmName+" covered "
        +tested+"/"+nTrans+" transitions ("+percent+"%).");
  }
}
