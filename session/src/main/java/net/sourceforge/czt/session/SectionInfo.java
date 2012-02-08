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

import java.util.Collection;
import java.util.Set;
import java.util.logging.Level;

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
 * 
 * @author Leo Freitas
 * @author Andrius Velykis
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
   * @throws CommandException if the lookup was unsuccessful.   
   */
  <T> T get(Key<T> key) throws CommandException;

  /**
   * <p>
   * Starts a section manager transaction. Adding computed results to a section manager requires a
   * transaction to be started for the result key. The transaction is then used to track
   * dependencies of the calculated value, i.e. what other objects were used to compute the result.
   * </p>
   * <p>
   * The section manager is updated with new results via transactions. So when computing a result to
   * cache in the section manager, a transaction needs to be started first, and then ended by
   * putting the computed result (see {@link #endTransaction(Key, Object)}). Alternatively, if the
   * computation fails, the started transaction needs to be cancelled (see
   * {@link #cancelTransaction(Key)}).
   * </p>
   * <p>
   * The transactional approach to section manager computations allows us to capture implicit
   * dependencies of the computed result. Between the start and end of transaction, all calls to
   * {@link #get(Key)} in the section manager are tracked. E.g. when typechecking a ZSect "foo", the
   * command retrieves the parsed ZSect via {@code #get(new Key<ZSect>("foo", ZSect.class))}, and
   * typecheck results of parent ZSects, among others. All these implicit dependencies through
   * {@link #get(Key)} calls are assigned to the transaction upon its end.
   * </p>
   * <p>
   * By default, the implementors of section manager Commands do not need to start the transactions
   * manually. The {@link #get(Key)} method starts the transaction automatically before the command
   * is executed - see {@link #get(Key)} for details. However, in some cases, e.g. when the
   * computations are started on-the-fly (as opposed to via section manager commands, e.g.
   * calculating LatexMarkupFunction during parse), the transactions need to be started by this
   * method (or {@link #ensureTransaction(Key)}). Other cases include postponing a transaction (see
   * {@link #postponeTransaction(Key, Key)}), and then manually starting a transaction in the
   * correct order.
   * </p>
   * <p>
   * <strong>Note that if a transaction is started manually, handling of its cancellation upon
   * exceptions needs to be done manually as well. See {@link #cancelTransaction(Key)} for details.
   * </strong>
   * </p>
   * <p>
   * The start/end/cancel transaction functionality supersedes the previous put() style of updating
   * the section manager. The {@link #put(Key, Object)} methods now are just a convenience for
   * starting and immediately ending the transaction.
   * </p>
   * <p>
   * In addition to transactions in the section manager, duplicate computations are no longer
   * allowed. This means that a transaction cannot be started if the result has already been cached
   * - it is required to remove the previous result before starting a new transaction. This is
   * necessary to get correct dependencies. During removal of the key, all dependant objects are
   * also cleaned from the section manager.
   * </p>
   * <p>
   * As part of the {@link #postponeTransaction(Key, Key)}, this method checks that the started
   * transaction is the one expected during the last {@link #postponeTransaction(Key, Key)}.
   * </p>
   * 
   * @param key
   *          The key of the new transaction, indicating start of computation for the result.
   * @throws SectionInfoException
   *           Unchecked exception if constraints for starting the transaction are violated:
   *           <ul>
   *           <li>{@code key} transaction cannot be already started - no overlapping transactions
   *           on the same key.</li>
   *           <li>{@code key} result cannot be cached - no duplicate/overwritten results.</li>
   *           <li>{@code key} must be the one indicated as "expected" in the last call of
   *           {@link #postponeTransaction(Key, Key)}.</li>
   *           </ul>
   * @see #endTransaction(Key, Object)
   * @see #cancelTransaction(Key)
   * @see #ensureTransaction(Key)
   */
  void startTransaction(Key<?> key) throws SectionInfoException;

  /**
   * <p>
   * Ensures that the indicated transaction is active in the section manager. The method checks if
   * this transaction is started, and starts one if it is not (using {@link #startTransaction(Key)}
   * ).
   * </p>
   * <p>
   * This method is used very similarly as the {@link #startTransaction(Key)}, however it does not
   * start a transaction if one has already been started. This can be used when it is not know if
   * the transaction has been started before, say, via a command.
   * </p>
   * <p>
   * Otherwise, the method is the same as {@link #startTransaction(Key)}, so refer to its comments
   * for details.
   * </p>
   * 
   * @param key
   *          The key of the transaction to start (or check has already been started).
   * @throws SectionInfoException
   *           Unchecked exception if constraints for ensuring the transaction are violated:
   *           <ul>
   *           <li>If {@code key} transaction has already been started, it must be the currently
   *           active transaction.</li>
   *           <li>If {@code key} transaction has not been started, see exception cases in
   *           {@link #startTransaction(Key)}.</li>
   *           </ul>
   * @see {@link #startTransaction(Key)}
   */
  void ensureTransaction(Key<?> key) throws SectionInfoException;

  /**
   * <p>
   * This is a convenience method: it calls #endTransaction(Key, T, Set) on an empty set of explicit dependencies.
   * </p>
   *
   * @param <T>
   * @param key
   * @param value
   * @throws SectionInfoException
   */
  <T> void endTransaction(Key<T> key, T value) throws SectionInfoException;

  /**
   * <p>
   * Ends the transaction for the given key and associates the calculated results to this key in the
   * managed database. All (implicit) dependencies are available on that key from this point. That is
   * all the keys dependants (e.g., downwards dependency) and dependencies (e.g., upwards dependency).
   * For instance, a parsed section bar with parent foo will add both foo and bar to the section manager.
   * Key ("foo", ZSect) will have bar as a dependant and prelude/toolkit as its dependencies. The set will
   * include all involved classes (e.g., OpTable, ThmTable, LatexMarkupFunction, ZSect, etc).
   * </p>
   * <p>
   * Extra explicit dependencies can be given by the user. This method is usually called at the end of
   * the corresponding command for the given key (e.g., it concludes the command calculation dependencies chain).
   * Explicit dependencies cannot be null, but might be empty. Value and key must not be null. Complex
   * or overlapping transaction scopes are possible, but need to be done with care, when mutual dependencies
   * could cause problems. See LatexMarkupFunctionCommand for an example. It depends on ParseUtils, which
   * depends on LatexMarkupFunctionCommand.
   * </p>
   * <p>
   * A SectionInfoException is thrown either if the transaction stack is empty or if there are no matching
   * transactions started for the given key. Otherwise, if there is a matching transaction for the key.
   * Implementations keeping track of implicit dependencies calculated throughout the transaction might
   * throw an exception in case the indexes/pointers for (sub-)dependencies within the transaction change
   * or are out of bounds. Before updating the managed database, a check that the key type T
   * matches / is an instance of the value type T is performed, where an exception is raise if they are
   * not compatible. Finally, if the key is already cached, an exception is also raised, given duplicates
   * or updates are not allowed in order to keep consistency checks straightforward (e.g., to update remove
   * than add the key again).
   * </p>
   *
   * @param <T>
   * @param key non null
   * @param value non null
   * @param explicitDependencies non null (possibly empty)
   * @throws SectionInfoException see above
   */
  <T> void endTransaction(Key<T> key, T value, Collection<? extends Key<?>> explicitDependencies) throws SectionInfoException;

  /**
   * <p>
   * Transactions can be cancelled due to some problem encountered. The effect they have is to revert the
   * database to the point right before the start of the transaction. Nevertheless, any successful transactions
   * in between this one <bf>are not</bf> rolled back. This means a cancelled transaction might result in a
   * partially successful one, if it contains sub transactions within. This is the desired behaviour because we
   * want to avoid redoing the successful bits if possible (e.g., if dependencies allow us to do so).
   * </p>
   * <p>
   * For instance, for a section bar with type errors bar and type correct parent foo, we would parse both
   * sections, type check foo and fail to type check bar. If possible (e.g., programatically or via on-the-fly paras)
   * to correct the errors in bar, we would not need to type check foo, but just reparse bar. TODO: is this what we want?
   * </p>
   * <p>
   * The set of keys returned represent the implicit keys leading to the failure. These include dependencies from
   * the start of the calculation. That will include keys of successful transactions.
   *
   * TODO: shouldn't this result be only for the keys involved in unsuccessful transactions?
   * </p>
   * @param key non null key that must be the top of the stack
   * @return set of implicit dependencies calculated during this transaction, including successful ones.
   * @throws SectionInfoException see above and #endTransaction(Key, T, Set).
   */
  Set<Key<?>> cancelTransaction(Key<?> key) throws SectionInfoException;

  /**
   * <p>
   * Postpones the just-started transaction to ensure a correct transaction order. This is used to
   * reorder transactions for complex commands, when the requested key (and thus started
   * transaction) will be calculated as part of another bigger transaction.
   * </p>
   * <p>
   * Some of the commands may calculate their results as part of a bigger calculation. The following
   * are several examples the illustrating need and use case for
   * {@link #postponeTransaction(Key, Key)}:
   * <dl>
   * <dt>Calculating the Latex Markup Function</dt>
   * <dd>The Latex Markup Function (LMF) is created while parsing a Z Section (ZSect). So if the Z
   * Section has not been parsed before, requesting a Latex Markup Function (via LatexMarkupCommand)
   * from the section manager will trigger parsing of the Z Section. In this case, the nested
   * calculations form the following transaction chain: LMF > ZSect > LMF. A cyclic chain is invalid
   * in the transactional section manager, and needs to be reordered. The
   * {@link #postponeTransaction(Key, Key)} method is used to perform this reorder, indicating that
   * the LMF transaction will be postponed in favor of the ZSect, which may in turn perform the LMF
   * transaction again (i.e., postponed).</dd>
   * <dt>Parsing a ZSect</dt>
   * <dd>The Latex and Unicode specifications are parsed as Spec, containing one or more ZSects. If
   * the section manager is asked to calculate a ZSect (via {@link #get(Key)}), the transactional
   * chain would be ZSect > Spec > ZSect. The initial ZSect transaction is postponed to get Spec >
   * ZSect.</dd>
   * <dt>Calculating the Info Tables</dt>
   * <dd>When parsing a ZSect, a number of info tables are calculated, such as operator table, joker
   * table (circus), etc. The cases are very similar to these of LMF. When the appropriate commands
   * are used, we would get a cyclic transactional chain, e.g. OpTable > ZSect > OpTable. By
   * postponing the initial transaction, we get ZSect > OpTable.</dd>
   * <dl>
   * </p>
   * <h4>Usage</h4>
   * <p>
   * This method is a strict version of the {@link #cancelTransaction(Key)}. It requires to indicate
   * the next expected transaction - it should be known when postponing. This will be verified when
   * the next transaction is started in {@link #startTransaction(Key)}. Furthermore, this method can
   * only be used for just-started transaction (which do not have any marked dependencies - no
   * {@link #get(Key)} calls since starting it). This constraint ensures that we are not losing any
   * dependencies by postponing.
   * </p>
   * <p>
   * Because of these constraints, postponing (and thus reordering) the transactions should be used
   * as the first action in the command. If an inappropriate transaction has been started within
   * {@link #get(Key)} right before launching the command, postponing it in favor of another
   * (larger) transaction allows to achieve the desired order.
   * </p>
   * 
   * @param postponedKey
   *          The key of an active transaction to be be postponed. The indicated transaction must be
   *          at the top of transaction stack (currently active). It will be cancelled by this
   *          method. The transaction cannot have any dependencies marked for it (via
   *          {@link #get(Key)}).
   * @param nextKey
   *          The key for the next expected transaction. Indicates the transaction that the
   *          postponed key is postponed in favor of. The next call to
   *          {@link #startTransaction(Key)} must match the indicated key.
   * @throws SectionInfoException
   *           Unchecked exception if constraints for postponing the transaction are violated:
   *           <ul>
   *           <li>{@code postponedKey} and {@code nextKey} cannot be null.</li>
   *           <li>{@code postponedKey} must be the currently active transaction.</li>
   *           <li>{@code postponedKey} cannot have dependencies marked for it (via
   *           {@link #get(Key)}).</li>
   *           <li>{@code nextKey} cannot be already cached.</li>
   *           <li>{@code nextKey} cannot be an already active transaction.</li>
   *           <li>There cannot be an already postponed transaction.</li>
   *           </ul>
   * @see #cancelTransaction(Key)
   * @see #startTransaction(Key)
   */
  void postponeTransaction(Key<?> postponedKey, Key<?> nextKey) 
      throws SectionInfoException;

  /**
   * checks whether there is any ongoing transaction for the given key
   * @param key
   * @return true if there is a transaction for key, false otherwise
   */
  boolean hasTransaction(Key<?> key);

  /**
   * Add a mapping from the key to its corresponding value. A set of explicit
   * dependant keys of (possibly different) type is also given. These dependencies,
   * together with any implicit dependencies involved are iterated to create map of
   * dependencies in both directions (e.g., the ones the key depend on as well as
   * the ones that depend on this key).
   *
   * @param <T> key type
   * @param key   The key to be looked up.
   * @param value value to map.
   * @param explicitDependencies dependant keys (i.e., the set of keys the key being put depend on - e.g., parents, downward dependency)
   * @throws SectionInfoException
   */
  <T> void put(Key<T> key, T value, Collection<? extends Key<?>> explicitDependencies) throws SectionInfoException;
  <T> void put(Key<T> key, T value) throws SectionInfoException;


  /**
   * Retrieve all the keys involving a given name (e.g., ZSect, Spec, Source, etc for given string name)
   * @param name
   * @return set of keys of all types with managed mappings
   */
  Set<Key<?>> keysOf(String name);

  /**
   * Retrieve all the keys involving a given class type
   * @param <T> type of key class
   * @param clsName
   * @return set of all keys of given type with managed mappings
   */
  <T> Set<Key<? extends T>> keysOf(Class<T> clsName);

  boolean isPermanentKey(Key<?> key);

  void reset();
  
  //SectInfo clone();

  /**
   * Checks whether the given key is cached within the section information manager
   * @param key The key to be looked up.
   * @return whether the key is cached or not
   */
  boolean isCached(Key<?> key);
  
  /**
   * Returns whether the given value has already been computed and is cached. It returns null if it hasn't.
   * Also, if the key queried is on an ongoing transaction this method  might throw an exception.
   * @param <T> returned key type
   * @param value value to search for key
   * @return value's associated key
   */  
  <T> Key<? super T> retrieveKey(T value);

  /**
   * <p>
   * Remove a given key and all its dependants. That is, if A parents B
   * B parents C and we remove B, it also removes C but not A. That is,
   * it removes all dependants of the given key.
   * </p>
   * <p>
   * An exception is thrown if the key being removed is part of any ongoing transaction.
   * In this case, nothing changes and the key and its dependants/dependencies is not removed.
   * </p>
   * 
   * @param key
   * @return if anything changed as a result of this call.
   * @throws SectionInfoException
   */
  boolean removeKey(Key<?> key) throws SectionInfoException;

  /**
   * <p>
   * Return all the elements that depend on the given key. That is,
   * A parents B, B parents C and the given key is for A, then the result
   * is B and C. This is the inverse (transitive) relation as parents.
   *</p>
   * <p>
   * An exception is thrown if the key being queried is part of any ongoing transaction.
   * </p>

   * @param key
   * @return
   * @throws SectionInfoException
   */
  Set<Key<?>> getDependants(Key<?> key) throws SectionInfoException;

  /**
   * <p>
   * Return all the elements that the given key depend on. That is,
   * A parents B, B parents C and the given key is for C, then the result
   * is A and B. This is the (transitive) relation of parents.
   *</p>
   * <p>
   * An exception is thrown if the key being queried is part of any ongoing transaction.
   * </p>
   * @param key
   * @return
   * @throws SectionInfoException
   */  
  Set<Key<?>> getDependencies(Key<?> key) throws SectionInfoException;

  /**
   * Set section management tracing on/off. Tracing information is useful for
   * debugging purposes of the get/put protocols involved. It is up to each
   * implementation how to achieve this. For instance, the <code>SectionManager</code>
   * uses a <code>ConsoleHandler</code> from the Java logging API.
   *
   * @param on flag to set it on or off
   * @param level
   * @return the previous value of tracing flag
   */
  boolean setTracing(boolean on, Level level);

  Level getTracingLevel();
}
