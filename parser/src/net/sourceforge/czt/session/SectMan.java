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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.Iterator;

public class SectMan
  implements Context, SectionInfo
{
  /**
   * The main contents.
   */
  private Map/*<Key,ContextEntry>*/ contents_ = new HashMap();

  /**
   * The default commands.
   */
  private Map/*<Class,Command>*/ defaultCommands_ = new HashMap();

  /** General interface for all undo operations. */
  private interface Undo
  {
    void undo(Map contents);
  }

  /** Records information for undoing a put command. */
  private class UndoPut implements Undo
  {
    private Key key_;

    /**
     * The entry PRIOR to the put (or null).
     */
    private ContextEntry oldEntry_;

    UndoPut(/*@non_null@*/Key key, ContextEntry e)
    {
      key_ = key;
      oldEntry_ = e;
    }

    public void undo(Map contents)
    {
      contents.remove(key_); // remove NEW entry
      if (oldEntry_ != null)
        contents.put(key_, oldEntry_);
    }
  }

  /** Records information for undoing a remove command. */
  private class UndoRemove implements Undo
  {
    private Key key_;

    /**
     * The entry PRIOR to the remove (or null).
     */
    private ContextEntry oldEntry_;

    UndoRemove(/*@non_null@*/Key key, ContextEntry e)
    {
      key_ = key;
      oldEntry_ = e;
    }

    public void undo(Map contents)
    {
      if (oldEntry_ != null)
        contents.put(key_, oldEntry_);
    }
  }

  private class UpdateLog
  {
    public Command currCmd;
    public Map currArgs;

    /** A list of the changes we may need to undo.
     *  Note: currently UndoPut and UndoRemove are so similar
     *  that we could merge them and not need the Undo interface.
     *  However, in the future there may be other kinds of updates
     *  to undo.  So we use the general solution.
     */
    public List/*<Undo>*/ updates;

    public UpdateLog(/*@non_null@*/Command cmd, /*@non_null@*/Map args)
    {
      currCmd = cmd;
      currArgs = args;
      updates = new ArrayList();
    }
  }

  /**
   * The commands that are currently updated.
   */
  private Stack/*<UpdateLog>*/ currentlyExecuting_ = new Stack();

  /** This is for backwards compatibility with SectionInfo. */
  public Object getInfo(String name, Class type)
  {
    Key key = new Key(name, type);
    return get(key);
  }

  /** Is there a default algorithm for calculating infoType? */
  public boolean isAvailable(Class infoType)
  {
    Command cmd = (Command) defaultCommands_.get(infoType);
    return cmd != null;
  }

  public Object get(Key key)
  {
    ContextEntry entry = (ContextEntry) contents_.get(key);
    if (entry == null) {
      Command cmd = (Command) defaultCommands_.get(key.getType());
      if (cmd != null) {
        Map args = new HashMap();
        args.put("input", key);
        try {
          update(cmd, args);
        }
        catch (Exception e) {
          e.printStackTrace();
        }
        entry = (ContextEntry) contents_.get(key);
      }
    }
    if (entry == null)
        return null;
    else
        return entry.getValue();
  }

  public void put(Key key, Object value, Set dependencies)
  {
    assert ! currentlyExecuting_.empty(); // we are inside update
    // TODO: check that all dependencies are valid and copy their 
    //       timestamps into a Key --> TimeStamp Map.
    //       This Map then goes into the new ContextEntry.

    UpdateLog log = (UpdateLog) currentlyExecuting_.peek();
    ContextEntry newEntry = new ContextEntry(value, dependencies,
                               log.currCmd, log.currArgs);
    ContextEntry oldEntry = (ContextEntry) contents_.put(key, newEntry);
    log.updates.add(new UndoPut(key, oldEntry));
    System.out.println("DEBUG push UndoPut(" + key + ","
      + (oldEntry == null ? "null" : oldEntry.getValue()) + ")");
  }

  public void remove(Key key)
  {
    assert currentlyExecuting_ != null;
    ContextEntry oldEntry = (ContextEntry) contents_.remove(key);
    if (oldEntry != null)
    {
      UpdateLog log = (UpdateLog) currentlyExecuting_.peek();
      log.updates.add(new UndoRemove(key, oldEntry));
    }
  }

  public boolean update(Command cmd, Map args)
    throws Exception
  {
    boolean result = false;
    UpdateLog log = new UpdateLog(cmd, args);
    currentlyExecuting_.push(log); // this must be popped before returning
    try {
      result = cmd.execute(this, args);
      assert log == currentlyExecuting_.peek();
      List updates = log.updates;
      currentlyExecuting_.pop();
      // This command has now completed successfully, so we append
      // its changes to those of the parent command, if there is one.
      if ( ! currentlyExecuting_.empty())
        ((UpdateLog) currentlyExecuting_.peek()).updates.addAll(updates);
    }
    catch (Exception ex) {
      // The command failed, so undo its updates in reverse order.
      assert log == currentlyExecuting_.peek();
      List updates = log.updates;
      for (int i = updates.size() - 1; i >= 0; i--) {
        Undo undo = (Undo) updates.get(i);
        System.out.println("DEBUG: undo " + undo);
        undo.undo(contents_);
      }
      currentlyExecuting_.pop();
      throw ex;  // rethrow the same exception
    }
    return result;
  }

  public Command setDefault(Class kind, Command command)
  {
    return (Command) defaultCommands_.put(kind, command);
  }

  /** For debugging purposes.  Prints all keys. */
  public String toString()
  {
    StringBuffer buf = new StringBuffer();
    Iterator i = contents_.keySet().iterator();
    while (i.hasNext()) {
      Key k = (Key) i.next();
      buf.append("\t" + k + "\t|->\t"
                 + ((ContextEntry) contents_.get(k)).getValue() + "\n");
    }
    return buf.toString();
  }
}
