/*
  Copyright (C) 2004 Petra Malik
  Copyright (C) 2004 Mark Utting
  This file is part of the czt project.

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

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

public class SectMan
  implements Context, SectionInfo
{
  /**
   * The main contents.
   * Map<Key,ContextEntry>
   */
  private Map contents_ = new HashMap();

  /**
   * Map<Class,Command>
   */
  private Map defaultCommands_ = new HashMap();

  /**
   * Stack<UpdateLog>
   */
  private Stack currentlyExecuting_ = new Stack();

  public Object getInfo(String name, Class type)
  {
    Key key = new Key(name, type);
    return lookup(key);
  }

  public boolean isAvailable(Class infoType)
  {
    Command cmd = (Command) defaultCommands_.get(infoType);
    if (cmd != null) return true;
    return false;
  }

  public Object lookup(Key key)
  {
    Object result = contents_.get(key);
    if (result == null) {
      Command cmd = (Command) defaultCommands_.get(key.getType());
      if (cmd != null) {
        Map args = new HashMap();
        args.put("name", key.getName());
        try {
          update(cmd, args);
        }
        catch(Exception e) {
          System.err.println(e.getMessage());
        }
        result = contents_.get(key);
      }
    }
    return result;
  }

  public ContextEntry put(Key key, ContextEntry value)
  {
    return (ContextEntry) contents_.put(key, value);
  }

  public ContextEntry remove(Key key)
  {
    return (ContextEntry) contents_.remove(key);
  }

  public boolean update(Command cmd, Map args)
  {
    // TODO: cleanup if this fails
    return cmd.execute(this, args);
  }

  public Command setDefault(Class kind, Command command)
  {
    return (Command) defaultCommands_.put(kind, command);
  }
}
