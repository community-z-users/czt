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

import java.util.Map;
import java.util.Set;

public interface Context
{
  /**
   * Find/compute an entry within the context.
   * Returns <code>null</code> if the context cannot find the requested
   * object, and cannot compute it.
   */
  //@ ensures \result != null ==> \result instanceof type;
  Object lookup(Key key);

  /**
   * Only for use by Commands, during update().
   * Associates the specified value with the specified key.
   *
   * @return previous value associated with specified key,
   *         or <code>null</code> if there was none.
   */
  //@ requires value instanceof type;
  ContextEntry put(Key key, ContextEntry value);

  /**
   * Only for use by Commands, during update().
   * @return The value associated with key (null if none).
   */
  ContextEntry remove(Key key);

  /**
   * The main entry point for updating the context.
   * This executes <code>cmd</code>, which may update the context.
   * If this throws an exception, the context is not changed.
   */
  boolean update(Command cmd, Map args);

  /**
   * Set the default command for computing objects of class <code>kind</code>.
   * @return the old command associated with <code>kind</code>.
   */
  Command setDefault(Class kind, Command command);
}
