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
import java.util.HashSet;
import java.util.Set;

/** Measures the percentage of Actions that have been tested.
 *  It also records the history of that coverage.
 *  That is, the graph of how the Action coverage increases
 *  versus the number of transitions executed.
 */
public class ActionCoverage implements CoverageMetric
{
  private Set<String> done_;
  private ArrayList<Float> history_;
  private int numActions_;

  public ActionCoverage(int numActions)
  {
    numActions_ = numActions;
    reset();
  }

  public void reset()
  {
    done_ = new HashSet<String>();
    history_ = new ArrayList<Float>(100);
    history_.add(0.0F);
  }
  
  public float getPercentage()
  {
    return (float) done_.size() / (float) numActions_;
  }

  public ArrayList<Float> getHistory()
  {
    return history_;
  }

  public void doneTransition(Transition tr)
  {
    done_.add(tr.getAction());
    history_.add(getPercentage());
  }

  public String toString()
  {
    return Float.toString(getPercentage() * 100.0F) + "%";
  }
}
