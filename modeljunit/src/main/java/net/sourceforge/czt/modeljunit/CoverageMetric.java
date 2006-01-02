/**
 Copyright (C) 2006 Mark Utting
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

import java.util.ArrayList;

/** An interface to a test coverage metric.
 *  TODO: add recordHistory(int frequency) method, for efficiency?
 */
public interface CoverageMetric
{
  /** Reset all coverage data, including history.
   *  However, you can assume that the model does not change.
   *  After calling this method, getPercentage() should return 0.0F,
   *  and history should contain just a single 0.0F, meaning that
   *  nothing has been covered yet.
   */
  public void reset();
  
  /** The coverage percentage so far. */ 
  public float getPercentage();
  
  /** Returns the change over time of the coverage. */
  public ArrayList<Float> getHistory();

  /** The testing process calls this after taking each transition. */
  public void doneTransition(Transition tr);
}
