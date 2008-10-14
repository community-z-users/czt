/**
 Copyright (C) 2007 Mark Utting
 This file is part of the CZT project.

 The CZT project contains free software; you can redistribute it and/or
 modify it under the terms of the GNU General Public License as published
 by the Free Software Foundation; either version 2 of the License, or
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

import net.sourceforge.czt.modeljunit.Transition;

/** An interface for objects that listen for model events.
 */
public interface ModelListener
{
  /** Get the short name that this listener is known by.
   *  This name is used to add a listener to a model or
   *  a Tester object and to lookup a listener.
   *  The name should be a short descriptive noun phrase,
   *  all in lowercase, should usually be less than 30 characters,
   *  and may contain spaces.
   */
  public String getName();

  /** Returns the model that this listener is listening to.
   *  This may be null if this listener is not yet attached to a model.
   *  As another example, the coverage metric within a CoverageHistory
   *  object should always have getModel()==null, because it receives
   *  events from the CoverageHistory wrapper rather than the model.
   */
  public Model getModel();

  /** Tell the listener which model it is listening to.
   *
   */
  public void setModel(Model model);

  // TODO: might need a startReset(boolean) too?

  /** The Model calls this after each reset(boolean) action.
   *  @param reason   An adjective that describe why the reset was done.
   *  @param testing  The parameter that was passed to the FsmModel reset call.
   */
  public void doneReset(String reason, boolean testing);

  /**
   *  The Model calls this after each guard evaluation.
   *  Note that this will be called even after an implicit guard
   *  (which always returns true) has been evaluated.
   *  The {@code enabled} boolean says whether the guard of action is
   *  enabled or not, while {@code value} gives the actual value returned
   *  by the guard method (0 for false, 1 for true, or other positive
   *  integer values for Markov chain guards).
   */
  public void doneGuard(Object state, int action, boolean enabled, int value);

  /** This is called just before an action is about to be executed.
   *  (The guard of that action is known to be true at this point).
   *
   * @param state  The current state of the model.
   * @param action The number of the action.
   * @param name   The name of the action.
   */
  public void startAction(Object state, int action, String name);

  /** The Model calls this after taking each transition.
   *
   * @param action  The number of the action just taken.
   * @param tr      The transition just taken.
   */
  public void doneTransition(int action, Transition tr);

  /** The Model calls this when an action has found an error.
   *  The failure exception contains lots of information about
   *  the test failure.  If a listener throws this exception, then
   *  the test generation process will stop with this exception.
   *  (after all listeners have been notified of the failure).
   */
  public void failure(TestFailureException failure);
}
