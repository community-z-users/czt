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

package net.sourceforge.czt.modeljunit.coverage;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import net.sourceforge.czt.jdsl.graph.api.Graph;
import net.sourceforge.czt.jdsl.graph.api.Vertex;
import net.sourceforge.czt.modeljunit.Transition;

/** A wrapper class that adds history recording to any CoverageMetric.
 *  This is useful for drawing graphs of how the coverage changes over
 *  time etc.
 *  For example, new CoverageHistory(new ActionCoverage(), 10)
 *  behaves exactly the same as the ActionCoverage metric, but
 *  also records a snapshot of its coverage level each 10 calls
 *  to doneTransition(...).
 *
 * @author marku
 */
public class CoverageHistory implements CoverageMetric
{
  /** How often to take a snapshot. */
  //@invariant interval_ > 0;
  private int interval_;

  /** Counts down from interval_ to 0. */
  private int count_;

  /** The underlying coverage metric. */
  private CoverageMetric metric_;

  /** Coverage snapshots are recorded in here. */
  private/*@non_null@*/List<Integer> history_;

  /** Create a history version of the coverage metric.
   *  It records the value of metric.getCoverage() each
   *  interval calls to doneTransition.
   *
   * @param metric   The coverage metric to add history to.
   * @param interval How often to take snapshots.
   */
  //@requires interval > 0;
  public CoverageHistory(/*@non_null@*/CoverageMetric metric, int interval)
  {
    interval_ = interval;
    metric_ = metric;
    history_ = new ArrayList<Integer>(100); // start with a reasonable size
    history_.add(0);
    count_ = interval_;
  }

  /** Returns the underlying coverage metric. */
  public/*@non_null@*/CoverageMetric getMetric()
  {
    return metric_;
  }

  /** Delegates to getMetric().getName(). */
  public String getName()
  {
    return metric_.getName();
  }

  /** Delegates to getMetric().getDescription(). */
  public String getDescription()
  {
    return metric_.getDescription();
  }

  /** This resets the history, as well as calling getMetric().reset(); */
  public void reset()
  {
    metric_.reset();
    count_ = interval_;
    history_.clear();
    history_.add(0);
  }

  /** Delegates to getMetric().setModel(...). */
  public void setModel(Graph model, Map<Object, Vertex> state2vertex)
  {
    metric_.setModel(model, state2vertex);
  }

  /** Delegates to getMetric().doneInit(...). */
  public void doneInit(boolean testing)
  {
    metric_.doneInit(testing);
  }

  /** Delegates to getMetric().doneTransition(...),
   *  and records the resulting coverage.
   */
  public void doneTransition(Transition tr)
  {
    metric_.doneTransition(tr);
    if (--count_ == 0) {
      history_.add(metric_.getCoverage());
      count_ = interval_;
    }
  }

  /** Returns getMetric().getCoverage(). */
  public int getCoverage()
  {
    return metric_.getCoverage();
  }

  /** Returns getMetric().getMaximum(). */
  public int getMaximum()
  {
    return metric_.getMaximum();
  }

  /** Returns getMetric().getPercentage(). */
  public float getPercentage()
  {
    return metric_.getPercentage();
  }

  /** Returns the list of coverage snapshots. */
  public List<Integer> getHistory()
  {
    return history_;
  }

  /** Returns getMetric().getDetails(). */
  public Map<Object, Integer> getDetails()
  {
    return metric_.getDetails();
  }

  /** Returns getMetric().toString(). */
  public String toString()
  {
    return metric_.toString();
  }

  /** Converts the history coverage values to a comma-separated string.
   * 
   * @return  A string, like "0,1,3,5,5,5"
   */
  public String toCSV()
  {
    StringBuffer result = new StringBuffer();
    for (Integer cov : history_) {
      result.append(",");
      result.append(cov);
    }
    return result.substring(1); // skip the first comma.
  }
}
