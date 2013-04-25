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
 * A section information (also called <i>section manager</i>) is the central place for storage and
 * computation of CZT information. The computed values are stored in the section manager and can be
 * referred to by subsequent computations.
 * <p>
 * The section manager provides three main functions:
 * <dl>
 * <dt>Caching computed values</dt>
 * <dd>Values can be stored in the section manager after calculation, and then can be retrieved via
 * {@link #get(Key)}. Their availability can be checked via {@link #isCached(Key)}.</dd>
 * <dt>Computing values using commands</dt>
 * <dd>The section manager provides a dynamic way of configuring how values are computed. Depending
 * on different dialects, or just configurations, the section manager can use different commands to
 * compute CZT objects. The commands are launched in {@link #get(Key)}, if the requested key is not
 * yet cached.</dd>
 * <dt>Tracking dependencies in a transactional way</dt>
 * <dd>The section manager can track dependencies of computed values, so that when they are removed,
 * the dependencies do not need to be recalculated. To facilitate correct dependency tracking, the
 * section manager employs a transactional model. When a computation of a certain CZT object starts,
 * its transaction should be started (see {@link #startTransaction(Key)}). Then the result value is
 * stored in the section manager by ending the transaction (see
 * {@link #endTransaction(Key, Object, Collection)}). If any problems occur during the computation,
 * the transaction is cancelled (see {@link #cancelTransaction(Key)}).</dd>
 * </dl>
 * </p>
 * <p>
 * The information is stored in the section manager by using keys, which are a pair of name and
 * value type. The section specific information should be identified by the section name, which
 * should be unique.
 * </p>
 * 
 * @author Leo Freitas
 * @author Andrius Velykis
 * @see #get(Key)
 * @see #startTransaction(Key)
 * @see #endTransaction(Key, Object, Collection)
 * @see #cancelTransaction(Key)
 * @see SectionManager The default section manager implementation
 */
public interface SectionInfo 
{
  /**
   * Looks up and resolves the {@code key} in the section manager. It never returns {@code null}. If
   * a key is present in the section manager (i.e., {@link #isCached(Key)}= {@code true}), the
   * cached value is returned. Otherwise, a command must be present in the section manager for the
   * indicated key type. It is used to compute the result for the given key and store in the section
   * manager. This value is returned after computation. If any problems during the process occur,
   * the {@link CommandException} is thrown.
   * <p>
   * The commands for different result types are configured dynamically in the section manager. See
   * {@link SectionManager#get(Key)} for details about some core commands and their keys.
   * </p>
   * <p>
   * Note that when a command is used to compute a result, it may have further calls to
   * {@link #get(Key)}, which would in turn create their own computations. Thus a single call to
   * this method may populate the section manager with a large amount of objects, depending on the
   * the computation dependencies.
   * </p>
   * <h4>Transactions & dependencies</h4>
   * <p>
   * This method is the main entry point to interaction with the section manager. All computations
   * should be done via the section manager commands, which would provide a good transactional
   * environment with clear dependencies. For that reason, this method plays an important part in
   * the default support for section management transactions, and dependency tracking.
   * </p>
   * <p>
   * If a result value for the given key is not available in the section manager, a command is used
   * to compute the value. This computation is wrapped in a start-cancel transaction. This means
   * that before the computation starts, a transaction for the {@code key} is started via
   * {@link #startTransaction(Key)}. Next, any exceptions caught during computation force the
   * cancellation of this transaction (see {@link #cancelTransaction(Key)}). Thus for the majority
   * of commands, they only need to end the successful transaction (via
   * {@link #endTransaction(Key, Object, Collection)}), and the starting/cancellation is handled
   * automatically.
   * </p>
   * <p>
   * On the other hand, this method is used to track dependencies for existing transactions. A call
   * to {@link #get(Key)} indicates that a computation requires a certain object from the section
   * manager. Thus the computation (and result value) depends on this object. The keys of all calls
   * to {@link #get(Key)} are collected for an existing transaction, and make up its implicit
   * dependencies. These calls may result in their own transactions started, if the value is not
   * computer, creating a nested tree of transactions, where "outer" transactions depend on "inner"
   * transactions and their values. The implicit dependencies are added to the key automatically,
   * when its transaction ends successfully.
   * </p>
   * 
   * @param <T>
   *          Type of the key, and the value which is be resolved.
   * @param key
   *          The key to be looked up and resolved.
   * @return An instance referenced by the key. If the value is cached in the section manager, it is
   *         returned. Otherwise, a command is used to compute this value and return it.
   * @throws CommandException
   *           If the lookup/resolution was unsuccessful:
   *           <ul>
   *           <li>No command is available to compute {@code key.getType()} value.</li>
   *           <li>The computation fails within the command.</li>
   *           <li>The computation does not provide a result.</li>
   *           </ul>
   * @throws SectionInfoException
   *           Unchecked exception if computation is required, but constraints for starting the
   *           transaction are violated (see {@link #startTransaction(Key)} for details).
   * @see SectionManager#get(Key)
   */
  <T> T get(Key<T> key) throws CommandException, SectionInfoException;

  
  /**
   * Starts a section manager transaction. Adding computed results to a section manager requires a
   * transaction to be started for the result key. The transaction is then used to track
   * dependencies of the calculated value, i.e. what other objects were used to compute the result.
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
   * typecheck results of parent ZSects, among others. These, in turn, will have implicit
   * dependencies on parent sections, etc. All these implicit dependencies through {@link #get(Key)}
   * calls are assigned to the transaction upon its end.
   * </p>
   * <h4>Usage</h4>
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
   * @see #get(Key)
   */
  void startTransaction(Key<?> key) throws SectionInfoException;

  
  /**
   * Ensures that the indicated transaction is active in the section manager. The method checks if
   * this transaction is started, and starts one if it is not (using {@link #startTransaction(Key)}
   * ).
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
   * @see #startTransaction(Key)
   */
  void ensureTransaction(Key<?> key) throws SectionInfoException;

  
  /**
   * Ends the transaction for the given key and associates the computed value to this key in the
   * section manager cache. Also marks the dependencies for the key. All implicit dependencies
   * (captured via {@link #get(Key)} calls since the start of transaction), as well as given
   * explicit dependencies are used.
   * <p>
   * The computed results can be stored in the section manager only as a part of the completed
   * transaction, using this method. This ensures strict contract on using the section manager, and
   * allows capturing implicit dependencies of the computation (see {@link #startTransaction(Key)}
   * for more details). Note that transaction can only be ended upon successful computation (when
   * the result is available). Otherwise, it must be cancelled.
   * </p>
   * <h4>Usage</h4>
   * <p>
   * Ending of transactions is the main method to use in section manager Commands. When the result
   * is calculated, it should be put into the section manager using this method. In the default
   * case, the starting and cancelling (upon exception) of transaction is handled inside
   * {@link #get(Key)}, thus only ending the transaction is required in the command.
   * </p>
   * <p>
   * <strong>Note that the transactions must be nested, and cannot overlap. So we can only end the
   * currently active transaction.</strong>
   * </p>
   * <p>
   * For the manually started transactions and exception-cancellation issues, please refer to
   * {@link #startTransaction(Key)} and {@link #cancelTransaction(Key)}.
   * </p>
   * <h4>Dependencies</h4>
   * <p>
   * As outlined in {@link #startTransaction(Key)}, all {@link #get(Key)} calls since the start of
   * transaction are collected as dependencies of this key. So in the case of parsing a ZSect, it
   * will collect dependencies on parent ZSects, its info tables, etc. These, in turn, will collect
   * their own dependencies on their parents, etc. This is achieved by a nesting of start-end of
   * transactions. The dependencies are stored in the section manager, and when one of the
   * dependencies is removed, this key is also (transitively) removed.
   * </p>
   * <p>
   * If some of the dependencies cannot be captured implicitly, the {@code explicitDependencies}
   * parameter allows indicating explicit dependencies. The following are several examples of such
   * cases:
   * <dl>
   * <dt>Complex order of transactions</dt>
   * <dd>Due to the complex nature of some commands (especially parsing), we cannot achieve a good
   * nested order of transaction. For example, lexing (and thus computation of LatexMarkupFunction)
   * can happen before the parsing (and computation of a ZSect). Thus we need to explicitly indicate
   * that ZSect depends on its LatexMarkupFunction.</dd>
   * <dt>Bi-directional dependencies</dt>
   * <dd>Section manager objects can be very closely inter-related, and we need bi-directional
   * dependencies. In this case, when one of the pair is removed, the other will be as well. Such
   * cases happen, e.g. for OpTable and its ZSect - the content of operator table is defined as
   * paragraphs of the Z section (OpTable depends on ZSect), however to correctly parse the
   * operators in a section, we need an oparator table (ZSect depends on OpTable). The explicit
   * dependencies allow including bi-directional dependencies.</dd>
   * </dl>
   * </p>
   * 
   * @param <T>
   *          The type of the computed {@code value}, as indicated by the {@code key}.
   * @param key
   *          The key referencing the {@code value} in the section manager. A transaction on this
   *          key must be started, and will be completed with this method.
   * @param value
   *          The computed value, which can be referenced by the {@code key} in the section manager
   *          afterwards. The value must exist and be of the type indicated by {@code key}.
   * @param explicitDependencies
   *          Explicit dependencies, if needed, for the indicated {@code key}.
   * @throws SectionInfoException
   *           Unchecked exception if constraints for ending the transaction are violated:
   *           <ul>
   *           <li>The parameters cannot be {@code null}.</li>
   *           <li>{@code key} transaction must be the currently active one.</li>
   *           <li>{@code key} result cannot be cached - no duplicate/overwritten results.</li>
   *           </ul>
   * @see #startTransaction(Key)
   * @see #cancelTransaction(Key)
   */
  <T> void endTransaction(Key<T> key, T value, Collection<? extends Key<?>> explicitDependencies)
      throws SectionInfoException;

  
  /**
   * This is a convenience method for {@link #endTransaction(Key, Object, Collection)}, with no
   * explicit dependencies. See {@link #endTransaction(Key, Object, Collection)} for details.
   * 
   * @param <T>
   *          The type of the computed {@code value}, as indicated by the {@code key}.
   * @param key
   *          The key referencing the {@code value} in the section manager. A transaction on this
   *          key must be started, and will be completed with this method.
   * @param value
   *          The computed value, which can be referenced by the {@code key} in the section manager
   *          afterwards. The value must exist and be of the type indicated by {@code key}.
   * @throws SectionInfoException
   *           Unchecked exception if constraints for ending the transaction are violated, see
   *           {@link #endTransaction(Key, Object, Collection)}.
   * @see #endTransaction(Key, Object, Collection)
   */
  <T> void endTransaction(Key<T> key, T value) throws SectionInfoException;
  
  
  /**
   * Cancels the ongoing transaction in the section manager. A transaction is usually cancelled if
   * an exception is thrown during computation of the result, or if the result cannot be computed
   * for other reasons. A cancelled transaction is no longer active, and results that depend on it
   * are removed from the section manager.
   * <p>
   * <strong>Note that cancelling a transaction does not remove successful nested transactions, if
   * they do not depend on the cancelled one.</strong> This means that after cancelling a top-level
   * transaction, there can still be "leftovers" from its dependencies.
   * </p>
   * <p>
   * For example, if we parse a Z section "bar {@code parents} foo". Thus a transaction for "bar"
   * ZSect is started, which in turn has a nested transaction to calculate its parent, "foo" ZSect.
   * If "bar" fails with a parse exception, we still want to keep the successfully parsed parent
   * "foo" ZSect. Then when the "bar" error is corrected, there is no need to re-parse "foo" ZSect.
   * Note that "foo" does not depend on "bar" in any way, so we can leave it in the section manager
   * when cancelling "bar".
   * </p>
   * <h4>Usage</h4>
   * <p>
   * By default, the implementors of section manager Commands do not need to cancel the transactions
   * manually. The {@link #get(Key)} method wraps the computation into a try-catch and cancels the
   * started transaction if an exception is encountered - see {@link #get(Key)} for details.
   * However, when the commands are started manually via {@link #startTransaction(Key)} (or
   * {@link #ensureTransaction(Key)}), there is a need to handle exceptions manually as well. If
   * possible, the paths that can throw exceptions should catch them, cancel the transaction, and
   * re-throw the exception.
   * </p>
   * <p>
   * This method can also be used to end the transaction, when the result cannot be calculated. In
   * this case, it should be somewhere alongside {@link #endTransaction(Key, Object, Collection)},
   * but cancelling if the {@code value} is {@code null} or invalid.
   * </p>
   * <p>
   * As a last resort, {@link #get(Key)} implementations should cancel all nested un-cancelled
   * transactions if caught in exceptions. However, for good transactional implementation, the
   * errors of manual transactions should be managed by the commands themselves.
   * </p>
   * 
   * @param key
   *          The key of currently active transaction, which needs to be cancelled. The key, and
   *          everything that depends on it, will be removed from the section manager.
   * @return Set of implicit dependencies captured since the start of this transaction, including
   *         the successful ones. They may be useful to track what the transaction depended on.
   * @throws SectionInfoException
   *           Unchecked exception if constraints for cancelling the transaction are violated:
   *           <ul>
   *           <li>{@code key} cannot be null.</li>
   *           <li>{@code key} transaction must be the currently active one.</li>
   *           </ul>
   * @see #startTransaction(Key)
   * @see #get(Key)
   */
  Set<Key<?>> cancelTransaction(Key<?> key) throws SectionInfoException;

  
  /**
   * Postpones the just-started transaction to ensure a correct transaction order. This is used to
   * reorder transactions for complex commands, when the requested key (and thus started
   * transaction) will be calculated as part of another bigger transaction.
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
   * Retrieves the currently active transaction.
   * 
   * @return The key for the currently active transaction, {@code null} otherwise.
   */
  Key<?> getCurrentTransaction();

  
  /**
   * Adds the value to the section manager cache. This is a shorthand method for starting and
   * immediately ending the transaction on the given {@code key}. This method should be used when
   * there is no computation of the value, and thus no implicit dependencies are needed. So by using
   * this method, the value is simply put in the section manager, indicating no gap in the
   * transaction.
   * <p>
   * Note that the method starts a transaction, thus it must not be used if a transaction is already
   * active. In that case, {@link #endTransaction(Key, Object, Collection)} must be used. Which is
   * the usual case for section manager commands.
   * </p>
   * <p>
   * The shorthand {@link #put(Key, Object, Collection)} method is good for putting things that do
   * not depend on anything in the section manager, e.g. initial Source objects. However, the method
   * allows indicating explicit dependencies in {@code explicitDependencies} parameter.
   * </p>
   * 
   * @param <T>
   *          The type of the {@code value}, as indicated by the {@code key}.
   * @param key
   *          The key referencing the {@code value} in the section manager. A transaction on this
   *          key must will be started and immediately ended with this method.
   * @param value
   *          The value, which can be referenced by the {@code key} in the section manager
   *          afterwards. The value must exist and be of the type indicated by {@code key}.
   * @param explicitDependencies
   *          Explicit dependencies, if needed, for the indicated {@code key} (e.g. the set of keys
   *          that the value depends on - parents, etc.).
   * @throws SectionInfoException
   *           Unchecked exception if constraints for starting and ending the transaction are
   *           violated. See {@link #startTransaction(Key)} and
   *           {@link #endTransaction(Key, Object, Collection)} for details.
   * @see #startTransaction(Key)
   * @see #endTransaction(Key, Object, Collection)
   */
  <T> void put(Key<T> key, T value, Collection<? extends Key<?>> explicitDependencies) throws SectionInfoException;
  
  
  /**
   * This is a convenience method for {@link #put(Key, Object, Collection)}, with no explicit
   * dependencies. Thus the call on this method indicates that the given {@code key} has no
   * dependencies altogether (neither implicit, nor explicit). See
   * {@link #put(Key, Object, Collection)} for details.
   * 
   * @param <T>
   *          The type of the {@code value}, as indicated by the {@code key}.
   * @param key
   *          The key referencing the {@code value} in the section manager. A transaction on this
   *          key must will be started and immediately ended with this method.
   * @param value
   *          The value, which can be referenced by the {@code key} in the section manager
   *          afterwards. The value must exist and be of the type indicated by {@code key}.
   * @throws SectionInfoException
   *           Unchecked exception if constraints for starting and ending the transaction are
   *           violated. See {@link #put(Key, Object, Collection)} for details.
   * @see #put(Key, Object, Collection)
   */
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


  /**
   * Resets the section manager. Resetting removes all cache and dependencies, except for the
   * "system" entries. The "system" entries include core CZT toolkits, e.g. "prelude" and
   * "*_toolkit".
   * <p>
   * Thus after resetting, there is no need to redo the work on CZT core toolkits.
   * </p>
   * <p>
   * The section manager cannot be reset if there are any ongoing transactions, because it will
   * destroy the transactional integrity.
   * </p>
   * 
   * @throws SectionInfoException
   *           Unchecked exception if there are ongoing transactions.
   */
  void reset() throws SectionInfoException;
  
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
   * Removes the key and its value from the section manager cache. All of key's dependants (other
   * keys that depended on it) are removed transitively as well.
   * <p>
   * For example, let {@code A parents B, B parents C}. Now if we remove {@code B} from the section
   * manager, it will also remove {@code A}, which depends on it, but not {@code C}. So now if we
   * want to recompute {@code B}, we no longer need to recompute {@code C}.
   * </p>
   * 
   * @param key
   *          The key to be removed, including all of its dependants. It cannot be part of an
   *          ongoing transaction.
   * @return {@code true} if the removal was successful, {@code false} if there was no cached value
   *         for the given {@code key}.
   * @throws SectionInfoException
   *           Unchecked exception if the {@code key} or any of its dependent keys are current in a
   *           transaction.
   */
  boolean removeKey(Key<?> key) throws SectionInfoException;

  /**
   * Retrieves keys of all elements that depend on the given {@code key}.
   * <p>
   * For example, let {@code A parents B}, {@code B parents C}. Then if {@code key} is for {@code C},
   * the result is {@code A} and {@code B}, because they depend on {@code C}.
   * </p>
   * <p>
   * Note that the relationship can be transitive, i.e. not all keys are returned would need to be
   * followed transitively to collect everything.
   * </p>
   * 
   * @param key
   *          The key, which dependants are requested.
   * @return Set of keys that depend on the given {@code key}.
   */
  Set<Key<?>> getDependants(Key<?> key);

  /**
   * Retrieves keys of all elements, that the given {@code key} depends on.
   * <p>
   * For example, let {@code A parents B}, {@code B parents C}. Then if {@code key} is for {@code A},
   * the result is {@code B} and {@code C}, because {@code A} depends on them.
   * </p>
   * <p>
   * Note that the relationship can be transitive, i.e. not all keys are returned would need to be
   * followed transitively to collect everything.
   * </p>
   * 
   * @param key
   *          The key, which dependencies are requested.
   * @return Set of keys, on which the given {@code key} depends.
   */  
  Set<Key<?>> getDependencies(Key<?> key);

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

  /**
   * Get current section manager tracing level as set by {@link #setTracing(boolean, Level)}.
   * @return current tracing level.
   */
  Level getTracingLevel();
  
  /**
   * Returns whether debugging tracing is on or not as set by {@link #setTracing(boolean, Level)}.
   * @return
   */
  boolean isTracing();
  
  /**
   * Returns the current language extension dialect is being managed (see {@link Dialect}). 
   * @return language extension being managed. This is immutable and should not change once set. 
   */
  Dialect getDialect();
}
