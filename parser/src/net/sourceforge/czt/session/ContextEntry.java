/*
  Copyright (C) 2004, 2005 Mark Utting
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

  private Set<Key> dependencies_;

  /**
   * The command that created <code>value</code>.
   */
  private Command createCmd_;

  /**
   * The arguments that createCmd had.
   */
  private Map createArgs_;

  /**
   * The timestamp of when this entry was created.
   */
  private TimeStamp createTime_;

  public ContextEntry(Object value, Set<Key> dependencies,
                      Command createCmd, Map createArgs)
  {
    value_ = value;
    dependencies_ = dependencies;
    createCmd_ = createCmd;
    createArgs_ = createArgs;
    createTime_ = new TimeStamp(); // the current time, but unique
  }

  public Object getValue()
  {
    return value_;
  }

  public Set<Key> getDependencies()
  {
    return dependencies_;
  }

  public Command getCreateCmd()
  {
    return createCmd_;
  }

  public Map getCreateArgs()
  {
    return createArgs_;
  }

  public TimeStamp getTimeStamp()
  {
    return createTime_;
  }
}
