/*
  Copyright (C) 2004, 2005 Mark Utting
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

import java.util.Map;
import java.util.Set;

/**
 * Context implementations manage a Key-to-Value mapping.
 * Their primary use is to manage all the Z data structures
 * used by a Z tool.  To run a Z command and update this context,
 * pass the Z command to the {@link #update} method.
 *
 * <p>
 * The keys are (String,Class) pairs, and the value that
 * a key (name,type) maps to will be an instance of type.
 * Context object also record and manage dependencies between
 * values, so that values can be automatically recalculated when
 * inputs change.
 */
public interface Context
{
  /**
   * Find/compute an entry within the context.
   * Returns <code>null</code> if the context cannot find the requested
   * object, and cannot compute it.
   * @param key The (String,Class) pair to find.
   * @return    If non-null, the result will be an instance of key.getType().
   */
  //@ ensures \result != null ==> \result instanceof key.getType();
  Object get(Key key);

  /**
   * Only for use by Commands, during update().
   * Associates the specified value with the specified key.
   * The dependencies are the set of keys whose values were
   * used during the production of the value.
   * If the value of some of those keys changes later on, this
   * value may be recalculated (using the Command and argument Map
   * that are currently being processed by update()).
   */
  //@ requires value instanceof key.getType();
  void put(Key key, Object value, Set/*<Key>*/ dependencies);

  /**
   * Only for use by Commands, during update().
   */
  void remove(Key key);

  /**
   * The main entry point for updating the context.
   * This calls <code>cmd.execute(this,args)</code>, which may update
   * this context using the {@link #put(Key,Object,Set)} and
   * {@link #remove(Key)} methods.
   * If this throws an exception (usually because
   * <code>cmd.execute(...)</code> throws an exception), the context
   * is not changed.  That is, all puts and removes associated with
   * cmd are undone.
   * This method can be called recursively.  The cmd and args of the
   * most recent call are called the <em>current</em> command and
   * arguments, and are associated with all changes via put and remove.
   */
  boolean update(Command cmd, Map args) throws Exception;

  /**
   * Set the default command for computing objects of class <code>kind</code>.
   * @return the old command associated with <code>kind</code>.
   */
  Command setDefault(Class kind, Command command);
}
