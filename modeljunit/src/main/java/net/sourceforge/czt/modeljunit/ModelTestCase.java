package net.sourceforge.czt.modeljunit;

import junit.framework.TestCase;
import java.lang.reflect.*;
import java.util.*;


/** Test a system, based on a finite state machine (FSM) model of that system.
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
 *    <li>It must have some <code>@transition void Meth(boolean testing)</code>
 *    methods.  These define the transitions of the FSM.  Each of these
 *    transition methods may change the state of the FSM, and when
 *    <code>testing</code> is true they should test some feature of the 
 *    underlying SUT and fail if errors are found.
 *    If <code>testing</code> is false, then we are just traversing the FSM
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
 *      public @transition void delete(boolean testing)
 *      {
 *        if (testing) {
 *          ... perform the SUT test and check results ...
 *        }
 *        fsmstate = ...new state of FSM...;
 *      }
 *    </pre>
 *    </li>
 *  </ol>
 *  </p> 
 */
public class ModelTestCase extends TestCase
{
  /** This class defines the finite state machine model of the system under test.
   *  It is null until fsmInit() has successfully loaded that class.
   */
  protected static Class fsmClass = null;
  
  /** The name of the finite state machine model that is being tested. */
  protected static String fsmName = null;
  
  /** The init method of fsmClass. */
  protected static Method fsmInit = null;
  
  /** All the @transition methods of fsmClass. */
  protected static ArrayList<Method> fsmTransitions = null;

  /** All the guards of fsmClass. 
   *  These are in exactly the same order as fmsTransitions.
   *  A null entry means that that transition methods has no guard. */
  protected static ArrayList<Method> fsmGuards = null;
  
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
  public static void fsmInit(/*@non_null@*/ Class fsm)
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
        if (paramTypes.length != 1
            || paramTypes[0] != boolean.class)
          fail("ERROR: @transition method "+fsmName+"."+m.getName()
              +" must take one boolean parameter."); 
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
    
    // now set fsmClass, to show that it is a valid FSM class.
    fsmClass = fsm;
  }

  /** An empty array of objects. */
  private static final Object[] fsmNoArgs = new Object[] {};
  
  /** Is transition number 'index' enabled?
   *  Returns 0.0 if transition number 'index' is disabled,
   *  or a positive number if it is enabled.
   *  Missing guard methods return 1.0F, while boolean guard methods
   *  return 1.0F when true and 0.0F when false.
   * @param  fsm    The instance of the FSM that is being tested.
   * @param  index  Index into the fsmTransitions array.
   * @return        The `enabledness' of this transition.
   */
  protected static float fsmEnabled(Object fsm, int index)
  {
    Method guard = fsmGuards.get(index);
    if (guard == null)
      return 1.0F; // missing guards are always true.
    Object result = null;
    try {
      result = guard.invoke(fsm, fsmNoArgs);
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
    fsmInit(fsm.getClass());
    int nTrans = fsmTransitions.size();
    BitSet transitionsTested = new BitSet(nTrans);
    BitSet transitionsTried = new BitSet(nTrans);
    try {
      // now traverse the FSM randomly
      int totalLength = 0;
      while (totalLength < length) {
        transitionsTried.clear();
        printProgress("STARTING SEARCH FOR TRANSITION");
        int next = rand.nextInt(nTrans);
        while (transitionsTried.cardinality() < nTrans) {
          while (transitionsTried.get(next))
            next = rand.nextInt(nTrans);
          printProgress("  Trying "+next);
          transitionsTried.set(next); // we have tried this one.
          Method m = fsmTransitions.get(next);
          if (fsmEnabled(fsm, next) > 0.0) {
            m.invoke(fsm, new Object[] {true});
            transitionsTested.set(next);
            totalLength++;
            printProgress("  TOOK TRANSITION "+next);
            break;
          }
          else
            printProgress("  (disabled) "+next);
        }
        if (transitionsTried.cardinality() == nTrans) {
          // we must reset the FSM to its initial state.
          printProgress("RESET TO INITIAL STATE");
          fsmInit.invoke(fsm, new Object[] {true});
        }
      }
    } catch (Exception e) {
      e.printStackTrace();
      Throwable cause = e.getCause();
      while (cause != null) {
        cause.printStackTrace();
        cause = cause.getCause();
      }
      fail(e.getMessage());
    }
    int tested = transitionsTested.cardinality();
    double percent = 100.0 * (double) tested / (double) nTrans;
    printProgress("RandomWalk testing of "+fsmName+" covered "
        +tested+"/"+nTrans+" transitions ("+percent+"%).");
  }

  public static void test1()
  {
    // fsmRandomWalk(new FSM(), 6, new Random());
    fsmRandomWalk(new FSM(), 10);
  }
  
  public static void main(String args[])
  {
    test1();
  }
}
