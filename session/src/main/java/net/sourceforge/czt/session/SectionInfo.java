/*
  Copyright (C) 2004 Petra Malik
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

import java.util.Set;

/**
 * <p>Provides information about sections.</p>
 *
 * <p>This interface provides a generic and extensible way
 * for applications to ask for all kinds of informations about
 * sections.  Sections are identified by its name, which should
 * be unique.  A SectionInfo object can provide a fixed set
 * of information, or can be generic in a way that classes
 * providing information about sections register there service.</p>
 *
 * <p>A SectionInfo object can cache the information provided,
 * but care should be taken when implementing such caches when
 * the information provided is mutable.</p>
 */
public interface SectionInfo
{
  /**
   * Lookup a key.
   * It should never return <code>null</code>.
   *
   * @param <T> key type
   * @param key   The key to be looked up.
   * @return An instance of key.getType().   
   * @throws CommandException if the lookup was unseccessful.   
   */
  <T> T get(Key<T> key) throws CommandException;

  /**
   * Add a mapping from the key to its corresponding value and set 
   * of dependant keys of (possibly different(?)) type.
   *
   * @param <T> key type
   * @param key   The key to be looked up.
   * @param value value to map.
   * @param dependencies dependant keys
   */
  <T> void put(Key<T> key, T value, Set<Key<?>> dependencies);

  /**
   * Checks whether the given key is cached within the section information manager
   * @param <T> key type
   * @param key The key to be looked up.
   * @return whether the key is cached or not
   */
  <T> boolean isCached(Key<T> key);
  
  /**
   * Returns whether the given value has already been computed 
   * and is cached. 
   * @param <T> returned key type
   * @param value value to search for key
   * @return value's associated key
   */  
  <T> Key<T> retrieveKey(T value);
}
