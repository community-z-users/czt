/*
  Copyright (C) 2004 Petra Malik
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
import java.util.Map;
import java.util.Set;

/**
 *  This class is used internally by SectMan.
 */
public class ContextEntry
{
  /**
   * The persistent value.
   */
  private Object value_;

  public Object getValue() { return value_; }

  /**
   * Set<Key>
   */
  private Set dependencies_;

  public Set/*<Key>*/ getDependencies() { return dependencies_; }

  /**
   * The command that created <code>value</code>.
   */
  private Command createCmd_;

  public Command getCreateCmd() { return createCmd_; }

  /**
   * The arguments that createCmd had.
   */
  private Map createArgs_;

  public Map getCreateArgs() { return createArgs_; }

  /** The (createDate_, createNum_) pair are the creation time-stamp.
   *  A Date alone is not precise enough, since it is quite likely
   *  that we will run two commands within the same millisecond.
   */
  private Date createDate_;

  /** The second part of the creation timestamp. */
  private int createNum_;

  /** Records the most recent Date() that was used by all instances. */
  static private Date lastDate_;

  /** A globally incrementing sequence counter for all instances.
   *  This is reset to 0 whenever Date() changes.
   */
  static private int lastNum_;

  /** True iff this entry was created after the other entry.
   *  If this==other, the result will be false.
   *  @param  other  The ContextEntry to compare against.
   *  @return true iff this.timestamp > other.timestamp.
   */
  public boolean newerThan(ContextEntry other)
  {
    int compare = createDate_.compareTo(other.createDate_);
    return compare > 0 || (compare == 0 && createNum_ > other.createNum_);
  }

  public ContextEntry(Object value, Set dependencies,
                      Command createCmd, Map createArgs)
  {
    value_ = value;
    dependencies_ = dependencies;
    createCmd_ = createCmd;
    createArgs_ = createArgs;

    // create a unique timestamp.
    createDate_ = new Date();  // the current time
    if (createDate_.equals(lastDate_))
	lastNum_ ++;
    else
	{
	  lastDate_ = createDate_;
	  lastNum_ = 0;
	}
    createNum_ = lastNum_;
  }
}
