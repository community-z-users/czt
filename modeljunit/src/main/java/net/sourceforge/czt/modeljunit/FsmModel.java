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

/** Interface for FSM models for model-based testing.
 * 
 *  The classes that implement this interface define
 *  Finite State Machine (FSM) models that are used for model-based
 *  test generation of unit tests (or of system tests).  The FSM model
 *  describes the expected behaviour of the underlying system under test
 *  (SUT), and can also act as an adaptor (a test harness) which calls
 *  the SUT methods and checks their results.
 *  
 *  
 *  Typically, each model
 *  will have some internal variables which define the current
 *  state of the model.  The <code>getState()</code> method
 *  must return a public view of those internal state variables,
 *  while the <code>reset(boolean)</code> method must reset those
 *  internal variables to their initial state.  In addition, the
 *  model should contain several `action' methods, like this:
 *  <pre>
 *  {@code @}Action public void myAction() {...}
 *  </pre>
 *  which modify the internal state of the FSM.  These correspond
 *  to the transitions (arcs) of the FSM model.  It is also possible
 *  to define a <em>guard</em> method on each of these action methods,
 *  to say when that action is enabled and when it is disabled.
 *  
 *   
 *  <p>
 *  The FSM model is written as a Java class that has some private state 
 *  variables and some public methods that act as the transitions of the FSM.
 *  It is often written as a wrapper around the system under test (SUT).
 *  This FSM class must obey the following rules: 
 *  <ol>
 *    <li>It must implement a <code>void reset(boolean testing)</code> method.  
 *    This must reinitialise the FSM to its initial state, and if the testing
 *    argument is true it must also reset the underlying SUT to its initial state.
 *    (It may create a new SUT instance on each call to init, or just once).
 *    <b>Advanced Feature:</b> If the SUT test part is expensive, then 
 *    you may like to save the reset(testing) flag and write all the 
 *    Action methods so that they do the SUT tests only after a reset(true) 
 *    call, and do nothing to the SUT after a reset(false) call.  
 *    However, they must still update the state of the model in both cases. 
 *    </li>
 *
 *    <li>It must implement a <code>getState()</code> method that returns
 *    a representation of the current state of the FSM.  The current state
 *    of the FSM is usually an <em>abstraction</em> (a simplified view) 
 *    of the current state of the underlying SUT.
 *    </li>
 *
 *    <li>It must have some <code>@Action public void Meth()</code>
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
 *    must return a boolean or integer value (the latter are used to define
 *    Markov chains for probabilistic testing). 
 *    The action method will only be called when its guard is true
 *    (or greater than 0 in the case of probabilistic guards). 
 *    So a typical action method with a guard will look like this:
 *    <pre>
 *      public boolean deleteGuard() { return ...; }
 *      {@code @}Action public void delete()
 *      {
 *        ... perform the SUT test and check results ...
 *        fsmstate = ...new state of FSM...;
 *      }
 *    </pre>
 *    </li>
 *  </ol>
 *  </p>
 
 *  
 * @author marku
 */
public interface FsmModel
{
  /** Return the current state of the FSM model.
   * 
   *  The objects returned by this method define the states
   *  (the nodes) of the finite state machine.  The objects that
   *  are returned must have a correct implementation of the equals
   *  method, since this is used to decide whether two states are
   *  the same or not.  It is common to return a string, but
   *  other kinds of objects can be used if desired (in which case,
   *  their toString() method will be used to get a printable form
   *  of each FSM state).
   *  <p>
   *  <b>Advanced Feature:</b> This method can be used to define 
   *  equivalence classes over the states, if you want to reduce
   *  the number of states to keep the FSM small.
   *  For example, if you have a integer state variable I that can
   *  have a huge number of possible values, you could define your
   *  getState() method to return <code>new Integer(I % 10)</code>.
   *  This would reduce the FSM to just 10 states, where FSM state 0
   *  represents all the states where I=0 or I=10 or I=20 etc., and
   *  FSM state 1 represents all the states where I=1 or I=11 or I=21 etc.
   *  </p>
   *
   * @return  An object that represents the current state.
   */
  public Object getState();

  /** Reset the model to its initial state.
   *  If the testing parameter is true, then this reset and all the
   *  following actions should affect the SUT.
   *
   * @param testing  true means the SUT should be reset too.
   */
  public void reset(boolean testing);
}
