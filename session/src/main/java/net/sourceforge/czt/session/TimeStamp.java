/*
  Copyright (C) 2004 Mark Utting
  This file is part of the CZT project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.session;

import java.util.Date;

/** This class implements precise timestamps and comparisons of them.
 * <p>
 *  Implementation Details:
 *  It uses a (Date, Counter) pair for the time-stamp, where
 *  the Counter is incremented each time one of these TimeStamp
 *  objects is created, to ensure uniqueness.
 *  A Date alone is not precise enough, since it is quite likely
 *  that we will run two commands within the same millisecond.
 *  To avoid int overflow, the Counter is reset to 0 each time
 *  that new Date() returns a new time.
 */
public class TimeStamp
{
  /** Records the most recent Date() that was used by all instances. */
  private static Date lastDate_;

  /** A globally incrementing sequence counter for all instances.
   *  This is reset to 0 whenever Date() changes.
   */
  private static int lastCount_ = 0;

  private static synchronized void incrementLastCount()
  {
	  lastCount_++;
  }
  
  private static synchronized void resetLastDate(Date d)
  {
	  assert d != null;
	  lastDate_ = d;
	  lastCount_ = 0;
  }
  
  private Date date_;

  /** The second part of the creation timestamp. */
  private int count_;

  public TimeStamp()
  {
    // create a unique timestamp.
    date_ = new Date();  // the current time
    if (date_.equals(lastDate_))
    	incrementLastCount();
    else {
    	resetLastDate(date_);
    }
    count_ = lastCount_;
  }

  /** True iff this entry was created after the other entry.
   *  If this==other, the result will be false.
   *  @param  other  The ContextEntry to compare against.
   *  @return true iff this.timestamp > other.timestamp.
   */
  public boolean newerThan(TimeStamp other)
  {
    int compare = date_.compareTo(other.date_);
    return compare > 0 || (compare == 0 && count_ > other.count_);
  }
}
