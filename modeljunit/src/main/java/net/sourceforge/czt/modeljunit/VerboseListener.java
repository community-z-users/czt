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

/** An implementation of ModelListener that prints
 *  events to System.out.
 */
public class VerboseListener extends AbstractListener
{
  public VerboseListener(Model model)
  {
    super(model);
  }

  public void doneReset(String reason, boolean testing)
  {
    model_.printMessage("done " + reason + " reset("+testing+")");
  }

  public void doneGuard(Object state, int action, boolean enabled, int value)
  {
  }

  public void startAction(Object state, int action, String name)
  {
  }

  public void doneTransition(int action, Transition tr)
  {
    model_.printMessage("done " + tr.toString());
  }

  public void failure(Exception ex)
  {
    model_.printMessage("FAILURE: "+ex.getLocalizedMessage());
  }
}
