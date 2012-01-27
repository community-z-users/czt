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
   * of dependant keys of (possibly different(?)) type. These dependencies
   * are iterated to create map of dependencies in both directions
   * (e.g., the ones the key depend on as well as the ones that depend on this key).
   *
   * @param <T> key type
   * @param key   The key to be looked up.
   * @param value value to map.
   * @param dependencies dependant keys (i.e., the set of keys the key being put depend on - e.g., parents, downward dependency)
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

  /**
   * Remove a given key and all its dependants. That is, if A parents B
   * B parents C and we remove B, it also removes C but not A. That is,
   * it removes all dependants of the given key.
   * 
   * @param key
   * @return if anything changed as a result of this call.
   */
  boolean removeKey(Key<?> key);

  /**
   * Return all the elements that depend on the given key. That is,
   * A parents B, B parents C and the given key is for A, then the result
   * is B and C. This is the inverse (transitive) relation as parents.
   *
   * @param key
   * @return
   */
  Set<Key<?>> getDependants(Key<?> key);

  /**
   * Return all the elements that the given key depend on. That is,
   * A parents B, B parents C and the given key is for C, then the result
   * is A and B. This is the (transitive) relation of parents.
   * @param key
   * @return
   */  
  Set<Key<?>> getDependencies(Key<?> key);

  /**
   * Set section management tracing on/off. Tracing information is useful for
   * debugging purposes of the get/put protocols involved. It is up to each
   * implementation how to achieve this. For instance, the <code>SectionManager</code>
   * uses a <code>ConsoleHandler</code> from the Java logging API.
   *
   * @param on flag to set it on or off
   * @return the previous value of tracing flag
   */
  boolean setTracing(boolean on);
}
