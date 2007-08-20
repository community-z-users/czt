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
  /** Returns the model that this listener is listening to. */
  public Model getModel();
  
  // TODO: might need a startReset(boolean) too?

  /** The Model calls this after each reset(boolean) action.
   *  @param reason   An adjective that describe why the reset was done.
   *  @param testing  true
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
   *  It is called just before the Model throws exception ex
   *  to report the error.
   */
  public void failure(Exception ex);
}
