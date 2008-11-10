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

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.modeljunit.coverage.CoverageMetric;

import junit.framework.Assert;


/** This class is a wrapper around a user-supplied EFSM model.
 *  It uses reflection to find all the actions and guards of the model.
 *  It allows a tester class (see {@link Tester} and its subclasses)
 *  to check the guards, call the actions and keep track of the current
 *  state.  It also provides a general listener facility that can be
 *  used to print progress messages, record model coverage metrics etc.
 *  <p>
 *  To use this wrapper, you write a special EFSM class
 *  (see {@link FsmModel}) that models part of the behaviour of
 *  your SUT, then pass an instance of that class to the constructor
 *  of this class.  Then you can pass an instance of this class to
 *  one of the {@link Tester} subclasses, such as {@link RandomTester},
 *  in order to generate/execute test sequences.  However, many of those
 *  classes provide a convenience constructor that creates this Model
 *  wrapper for you.
 *  </p>
 *  TODO: cache the guard evaluations?  This would give a small efficiency gain
 *     and would avoid calling the listeners several times for the same guard.
 */
public class Model
{
  /** The version of ModelJUnit */
  public static final String getVersion()
  {
    return "1.1";
  }

  /** This class defines the finite state machine model of the system under test.
   *  It is null until loadModelClass() has successfully loaded that class.
   */
  private Class<? extends FsmModel> fsmClass_ = null;

  /** The name of the finite state machine model that is being tested. */
  private String fsmName_ = null;

  /** The implementation under test (null means none yet). */
  //@invariant fsmModel_ != null ==> fsmClass_ != null;
  protected FsmModel fsmModel_ = null;

  /** All the @Action methods of fsmClass_. */
  //@invariant fsmActions_ == null <==> fsmClass_ == null;
  protected ArrayList<Method> fsmActions_ = null;

  /** All the guards of fsmClass_.
   *  These are in exactly the same order as fsmActions_.
   *  A null entry means that that Action method has no guard. */
  //@invariant fsmGuards_ == null <==> fsmClass_ == null;
  //@invariant fsmGuards_ != null ==> fsmGuards_.size() == fsmAction_.size();
  private ArrayList<Method> fsmGuards_ = null;

  /** Coverage listeners. */
  private Map<String,ModelListener> listeners_
    = new HashMap<String,ModelListener>();

  /** The current state of the implementation under test. */
  //@invariant fsmState_ != null ==> fsmModel_ != null;
  protected Object fsmState_ = null;

  /** True means we are generating real tests.
   *  False means we are just exploring the model,
   *  so the FsmModel does not really need to connect to the SUT.
   */
  private boolean fsmTesting_ = true;

  /** The initial state of the implementation under test. */
  //@invariant fsmInitialState_ == null <==> fsmState_ == null;
  private Object fsmInitialState_ = null;

  /** Current test sequence
   *  TODO: decide whether this needs to be builtin or a listener.
   */
  //@invariant fsmSequence_ == null <==> fsmModel_ == null;
  protected ArrayList<Transition> fsmSequence_;

  /** An empty array of objects. */
  protected static final Object[] VOID_ARGS = new Object[] {};

  /** Output device used for messages and warnings. */
  protected Writer output_;

  /** Constructs an EFSM model from the given FsmModel object.
   * @param model
   */
  public Model(FsmModel model)
  {
    // unbuffered, so that messages/warning appear ASAP.
    output_ = new OutputStreamWriter(System.out);
    loadModelClass(model.getClass());
    fsmModel_ = model;
    doReset("Initial"); // TODO: remove the need for this.  Do it later/never
  }

  /** Looks up an Action by name and returns its number.
   *  The resulting number can be used to execute an action
   *  (see {@link #doAction}) or to check the guard of the
   *  action (see {@link #isEnabled(int)}).
   *
   * @param name The name of an Action.
   * @return     The number of the action (>= 0), else -1.
   */
  //@requires fsmClass_ != null;
  //@requires name != null;
  //@ensures -1 <= \result && \result < fsmActions_.size();
  //@ensures \result >= 0 ==> name.equals(fsmActions_.get(i).getName());
  public int getActionNumber(String name)
  {
    for (int i=0; i < fsmActions_.size(); i++) {
      if (name.equals(fsmActions_.get(i).getName()))
        return i;
    }
    return -1;
  }

  /** Returns the FSM class that is the test model. */
  public Class getModelClass()
  {
	  return fsmClass_;
  }

  /** Returns the name of the FSM class that is the test model. */
  public String getModelName()
  {
	  return fsmClass_.getName();
  }

  /** Returns the model object that is begin tested. */
  public Object getModel()
  {
	  return fsmModel_;
  }

  /** Returns the current state of the implementation under test. */
  public Object getCurrentState()
  {
    return fsmState_;
  }


  /** Returns the name of the given Action. */
  //@requires fsmGetModelClass() != null;
  public String getActionName(int index)
  {
	  return fsmActions_.get(index).getName();
  }

  /** The total number of Actions. */
  //@requires fsmGetModel() != null;
  public int getNumActions()
  {
	  return fsmActions_.size();
  }

  /** True means we are generating real tests.
   *  False means we are just exploring the model,
   *  so the FsmModel does not really need to connect to the SUT.
   *  This flag is passed to each reset of the FsmModel.
   */
  public boolean getTesting()
  {
    return fsmTesting_;
  }

  /** Sets the testing flag.
   *  Returns its previous value.
   */
  public boolean setTesting(boolean testing)
  {
    boolean old = fsmTesting_;
    fsmTesting_ = testing;
    return old;
  }

  /** The current output stream, which is used for messages and warnings. */
  public Writer getOutput()
  {
    return output_;
  }

  /**
   * Sets the current output stream.
   * @param output
   * @return        the old output stream
   */
  public Writer setOutput(Writer output)
  {
    Writer old = output_;
    output_ = output;
    return old;
  }

  /** Loads the given class and finds its @Action methods.
   *  This method must be called before any fsm traversals are done.
   */
  protected void loadModelClass(/*@non_null@*/ Class fsm)
  {
    if (fsmClass_ == fsm)
      return;  // done already
    fsmClass_ = null;
    fsmName_ = fsm.getName();
    fsmActions_ = new ArrayList<Method>();
    for (Method m : fsm.getMethods()) {
      if (m.isAnnotationPresent(Action.class)) {
        Class[] paramTypes = m.getParameterTypes();
        if (paramTypes.length != 0)
          Assert.fail("ERROR: @Action method "+fsmName_+"."+m.getName()
              +" must have no parameters.");
        if (m.getReturnType() != void.class)
          printWarning("@Action method "
              +fsmName_+"."+m.getName()+" should be void.");
        // insert m into fsmActions_ in alphabetical order.
        int pos=0;
        while (pos < fsmActions_.size()) {
          if (fsmActions_.get(pos).getName().compareTo(m.getName()) > 0) {
            break;
          }
          pos++;
        }
        //System.out.println("adding method "+m.getName()+" at pos "+pos);
        fsmActions_.add(pos, m);
      }
    }
    int nActions = fsmActions_.size();
    if (nActions == 0) {
      Assert.fail("ERROR: FSM model "+fsmName_+" has no methods annotated with @Action.");
    }
    // Now look for guards of the Action methods.
    fsmGuards_ = new ArrayList<Method>(nActions);
    for (int i=fsmActions_.size(); i>0; i--) {
      fsmGuards_.add(null);  // all guards are null by default
    }
    for (Method m : fsm.getMethods()) {
      if (m.getName().endsWith("Guard")
          && m.getParameterTypes().length == 0) {
        String trName = m.getName().substring(0, m.getName().length()-5);
        int trPos = getActionNumber(trName);
        if (trPos < 0)
          printWarning(fsmName_+"."+m.getName()
              +" guard does not match any Action method.");
        else if (m.getReturnType() != boolean.class
              && m.getReturnType() != int.class) {
          printWarning("guard method "+fsmName_+"."+m.getName()
              +" must return boolean or int.");
        }
        else {
          fsmGuards_.set(trPos, m);
          //System.out.println("set guard["+trPos+"] := "+fsmName_+"."+m.getName());
        }
      }
    }
    // now set fsmClass_, to show that it is a valid FSM class.
    fsmClass_ = fsm;
  }

  /** Reset the FSM to its initial state.
   *  This is equivalent to doReset("User",testing),
   *  because it corresponds to a user-requested reset.
   */
  public void doReset()
  {
    doReset("User");
  }

  /** Reset the FSM to its initial state.
   *  This also calls the doneReset(reason, testing)
   *  method of all the listeners.
   *
   *  TODO: enhance it so that it gives no-guards-enabled and
   *        guards-not-deterministic warnings in the initial state.
   *
   * @param reason  Why the reset was performed (an adjective).
   */
  public void doReset(String reason)
  {
    if (fsmSequence_ == null) {
      fsmSequence_ = new ArrayList<Transition>();
    }
    else {
      //this.printProgress(1, "tested "+fsmSequence_.size()+" transitions.  "
      //    +reason+" reset from state "+fsmState_);
    }
    try {
      fsmModel_.reset(fsmTesting_);
      fsmSequence_.clear();
      fsmState_ = fsmModel_.getState();
      Assert.assertNotNull("Model Error: getState() must be non-null", fsmState_);
      if (fsmInitialState_ == null) {
        fsmInitialState_ = fsmState_;
      }
      else {
        Assert.assertEquals("Model error: reset did not return to the initial state",
            fsmInitialState_, fsmState_);
      }
      notifyDoneReset(reason, fsmTesting_);
    } catch (Exception ex) {
      throw new RuntimeException("Error calling the FSM reset method", ex);
    }
  }

  /**
   * True iff the current state is the initial state.
   * (Note that the result is false before the first reset,
   * since the initial and current state are unknown until then).
   * @return true if current state is the initial state.
   */
  public boolean isInitialState()
  {
    return fsmInitialState_ != null && fsmInitialState_.equals(fsmState_);
  }

  /** Is Action number 'index' enabled?
   *  Returns true if Action number 'index' is enabled.
   *  That is, if enabled(index) > 0.
   */
  public boolean isEnabled(int index)
  {
    return enabled(index) > 0;
  }

  /** Is Action number 'index' enabled?
   *  Returns 0 if Action number 'index' is disabled,
   *  or a positive number if it is enabled.
   *  Missing guard methods return 1, while boolean guard methods
   *  return 1 when true and 0 when false.
   * @param  index  Index into the fsmActions_ array.
   * @return        The `enabledness' of this Action.
   */
  public int enabled(int index)
  {
    assert 0 <= index;
    assert index < fsmGuards_.size();
    int result = 0;
    Method guard = fsmGuards_.get(index);
    if (guard == null) {
      result = 1; // missing guards are always true.
    }
    else {
      Object value = null;
      try {
        value = guard.invoke(fsmModel_, VOID_ARGS);
      }
      catch (Exception ex) {
        Assert.fail("Exception while calling guard " + guard.getName() + ", "
            + ex);
      }
      if (guard.getReturnType() == boolean.class) {
        if (((Boolean) value).booleanValue())
          result = 1;
        else
          result = 0;
      }
      else {
        result = ((Integer) value).intValue();
      }
    }
    notifyDoneGuard(fsmState_, index, result > 0, result);
    return result;
  }

  /** Return a fresh BitSet of all actions that are enabled
   *  in the current state.  Callers are free to mutate the result.
   */
  public BitSet enabledGuards()
  {
    BitSet enabled = new BitSet();
    for (int i=0; i < fsmActions_.size(); i++) {
      if (isEnabled(i))
        enabled.set(i);
    }
    return enabled;
  }

  /**
   *  True iff the current state is a terminal state.
   *  That is, if there are no transitions out of it.
   *  Note that the terminal status of a given state may depend
   *  upon the path taken to reach that state, so on one run a
   *  state may be terminal, whereas on another run it may not be.
   *
   * @return true iff getCurrentState() is a terminal state.
   */
  public boolean isTerminal()
  {
    return enabledGuards().cardinality() == 0;
  }

  /** Try to take the given Action from the current state.
   *  Returns true if the Action was taken, false if it was disabled.
   * @param  index  Index into the fsmTransitions array.
   * @return        True if taken, false if it is disabled.
   */
  public boolean doAction(int index)
  {
    if (! isEnabled(index))
    	return false;

    Method m = fsmActions_.get(index);
    try {
      notifyStartAction(fsmState_, index, m.getName());
      m.invoke(fsmModel_, VOID_ARGS);
    }
    catch (InvocationTargetException ex) {
      String failmsg = "failure in action "+m.getName()
      +" from state "+this.fsmState_+" due to "+ex.getCause();
      // TODO: find out why setting the cause here is not enough
      //     to make the cause's stack trace appear in the junit output.
      TestFailureException failure =
        new TestFailureException(failmsg, ex.getCause());
      failure.setActionName(m.getName());
      failure.setModel(this.fsmModel_);
      failure.setModelName(this.getModelName());
      failure.setSequence(this.fsmSequence_);
      failure.setState(this.fsmState_);
      notifyFailure(failure);

      /* Here is an alternative which throws just the original exception.
       * However, this does not allow us to add the model path like above.

        if (ex.getCause() != null
            && ex.getCause() instanceof AssertionFailedError) {
          AssertionFailedError origEx = (AssertionFailedError) ex.getCause();
          throw origEx;
        }
       */

      /*
      printFailure(2, failmsg);
      if (3 <= failureVerbosity && this.fsmSequence != null) {
        // print the sequence in reverse order, like a stacktrace
        for (int i=this.fsmSequence.size()-1; i>=0; i--)
          printFailure(3, "  after "+this.fsmSequence.get(i));
        printFailure(3, "  after reset.");
      }
      */
      // NOTE: we do not throw the failure exception here.
      //       Instead, each listener can decide to throw it or not.
    }
    catch (IllegalAccessException ex) {
      Assert.fail("Model Error: Non-public actions? "+ex);
    }
    Object newState = fsmModel_.getState();
    Transition done = new Transition(fsmState_, m.getName(), newState);
    fsmSequence_.add(done);
    fsmState_ = newState;
    Assert.assertNotNull("Model Error: getState() must be non-null", fsmState_);
    notifyDoneTransition(index, done);
    return true;
  }

  /** Add a listener.
   *  The listener name is used to identify it and retrieve it.
   *  If a listener by the same name is already present, then this
   *  new listener will be ignored.  This means that if you
   *  add the same listener multiple times, the first instance
   *  is the one that will continue to be used.  (So you get more
   *  of the graph or coverage statistics recorded).
   *
   *  @return The listener that will be used.
   */
  public ModelListener addListener(ModelListener listen)
  {
    ModelListener result = listeners_.get(listen.getName());
    if (result == null) {
      result = listen;
      listeners_.put(listen.getName(), listen);
      listen.setModel(this);

      if (listen instanceof CoverageMetric) {
        // see if we can tell this metric about the complete graph.
        GraphListener graph = (GraphListener) listeners_.get("graph");
        if (graph != null && graph.isComplete()) {
          ((CoverageMetric)listen).setGraph(graph.getGraph(), graph.getVertexMap());
        }
      }
    }
    return result;
  }

  /** Add one of the predefined model listeners or coverage metrics.
   *  For example, if name is "transition coverage", then a TransitionCoverage
   *  metric will be added to this model, and returned.
   *  However, if this model already has a listener by this name,
   *  then that listener will be returned and no new listener will be added.
   *
   * @param name The informal lowercase name of a Listener object.
   * @return     The listener that will actually be used.
   * @throws RuntimeException if name is not a known kind of listener.
   */
  public ModelListener addListener(String name)
  {
    ModelListener listen = ListenerFactory.getFactory().getListener(name);
    if (listen != null) {
      return addListener(listen);
    }
    throw new RuntimeException("Unknown kind of listener: " + name);
  }

  /** Remove a coverage listener by name.
   * @return the ModelListener that was removed (null if it was not present).
   */
  public ModelListener removeListener(String name)
  {
    return listeners_.remove(name);
  }

  /** Remove all coverage listeners. */
  public void removeAllListeners()
  {
    listeners_.clear();
  }

  /** Get the GraphListener for this model.
   *  This is equivalent to getListener("graph"), with a cast
   *  of the resulting listener to a GraphListener.
   *  @return null if this model has no graph listener.
   */
  public GraphListener getGraphListener()
  {
    return (GraphListener) getListener("graph");
  }

  /** Get a listener by name, or null if that name is unused.
   *
   *  @param name  The name of a listener.
   *  @return      null if name is not mapped to any listener.
   */
  public ModelListener getListener(String name)
  {
    return listeners_.get(name);
  }

  /** The set of names of all the current coverage metrics and listeners */
  public Set<String> getListenerNames()
  {
    return listeners_.keySet();
  }

  /** Sends a doneReset event to all listeners */
  public void notifyDoneReset(String reason, boolean testing)
  {
    // System.out.println("Done reset "+reason);
    for (ModelListener cm : listeners_.values())
      cm.doneReset(reason, testing);
  }

  /** Sends a doneGuard event to all listeners */
  public void notifyDoneGuard(Object state, int action,
      boolean enabled, int value)
  {
    for (ModelListener cm : listeners_.values())
      cm.doneGuard(state, action, enabled, value);
  }

  /** Sends a startAction event to all listeners */
  public void notifyStartAction(Object state, int action, String name)
  {
    for (ModelListener cm : listeners_.values())
      cm.startAction(state, action, name);
  }

  /** Sends a doneTransition event to all listeners */
  public void notifyDoneTransition(int action, Transition tr)
  {
    // System.out.println("Done action="+action+" Transition "+tr);
    for (ModelListener cm : listeners_.values())
      cm.doneTransition(action, tr);
  }

  /** Sends a failure event to all listeners.
   *  If one or more listeners throw a TestFailureException,
   *  then this method throws that exception, after all listeners
   *  have been informed of the failure.
   *  
   *  @throws TestFailureException if a listener throws it.
   */
  public void notifyFailure(TestFailureException ex)
  {
    // Any listener can decide to throw an exception.  However,
    // we send to ALL listeners before we throw any test failure exception.
    TestFailureException failure = null;
    for (ModelListener cm : listeners_.values()) {
      try {
        cm.failure(ex);
      }
      catch (TestFailureException fail) {
        failure = fail;
      }
    }
    if (failure != null) {
      throw failure;
    }
  }

  /** Prints a warning message to the current output writer.
   */
  public void printWarning(String msg)
  {
    printMessage("Warning: " + msg);
  }

  /** Print a message to the current output writer (see {@link #getOutput()}).
   *  This automatically adds a newline on the end of msg.
   *  It does a flush after each call, so that messages appear promptly.
   */
  public void printMessage(String msg)
  {
    try {
      output_.write(msg);
      output_.write('\n');
      output_.flush();
    }
    catch (IOException ex) {
      throw new RuntimeException("I/O error while printing message: "+msg, ex);
    }
  }
}
