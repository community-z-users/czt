/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.util.SimpleFormatter;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.Stack;
import java.util.Map.Entry;
import java.util.logging.ConsoleHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import net.sourceforge.czt.util.Pair;

/**
 * <p>
 * This class is a repository for information about (Z) specs/sections (and its extensions). It
 * stores all the objects used during CZT processing, such as parsed ASTs (abstract syntax trees)
 * type environments, and so on. It provides several services, depending on the kind of key
 * requested. For instance, it can compute the operator table or the LaTeX markup function for a
 * given section, or typecheck or domain check a given Term/Spec/ZSect. The keys to access an object
 * within the section manager are a (Name,Class) pair (see {@link Key}), which means that several
 * different kinds of objects can be associated with the same name.
 * </p>
 * <h3>Dependencies of cached objects</h3>
 * <p>
 * One of the main goals of this class is to cache commonly used objects, such as the parsed ASTs of
 * toolkit sections, so that they do not have to be repeatedly processed. This can give great
 * performance improvements. For instance, we envisage one section manager per project, where a
 * project is a collection of files representing sections (e.g., an IDE project like in
 * Netbeans/Eclipse).
 * </p>
 * <p>
 * Nevertheless, a fundamental problem is that data can become inconsistent if you add a section
 * {@code A}, then add other sections that uses it (e.g., {@code B parent A}, so that {@code B}
 * depends on {@code A}). If A changes, it <strong>must</strong> be invalidated within the section
 * manager and have its new version reloaded. Its dependent information must also be reloaded (e.g.
 * {@code B} may not be the same if {@code A} changes.
 * </p>
 * <p>
 * Our current solution is to have transactions that compute implicit dependencies whilst computing
 * information, as well as explicit (extra) dependencies given by the user. This dependency
 * calculation is quite hard to get right and this is an experimental feature at the moment. That
 * is, the safest choice is to keep fresh(er) section managers if that is of concern (i.e., have
 * section managers per file/buffer rather than projects) greater than performance gains.
 * </p>
 * <p>
 * We track duplicate objects as well as transaction scopes raising SectionManagerException at
 * appropriate places. We are still experimenting with the best approach. The section manager also
 * contain tracing methods to enable better debugging: tracing data is added to the console or
 * Logger handler in order to output all information stored during transaction processing.
 * </p>
 * <h3>Usage</h3>
 * <p>
 * There are currently three ways of getting/reusing a section manager object.
 * <ol>
 * <li>{@code new SectionManager(Dialect)} - which starts with an empty cache, so gives you the overhead of
 * parsing toolkits again.</li>
 * <li>{@code oldSectMan.reset()} - this clears everything in the cache, except for the prelude and
 * any sections called *_toolkit.</li>
 * <li>{@code oldSectMan.clone()} - depending upon WHEN you do this clone, you can decide just how
 * much you want to leave in the cache.</li>
 * </ol>
 * To avoid reparsing toolkits repeatedly (which makes things slow!), you should avoid creating new
 * section managers and use the reset or clone methods instead. Moreover, you can pass the Z dialect
 * the section manager is responsible for. That (dynamically) determines (via class loading at run
 * time) what tools will be used for parsing, typechecking, etc.
 * </p>
 * <p>
 * As well as the main cache of specification-related objects, this class maintains several other
 * kinds of information, including:
 * <ul>
 * <li>a <em>properties</em> map that stores a string value for various property keys (see
 * getProperty and setProperty)</li>
 * <li>a <em>command</em> map that stores a Command object for each kind of specification-related
 * type of interest. These Command objects are called when the section manager needs to calculate a
 * given type of object key and it is not already in the cache (see putCommand).</li>
 * </ul>
 * </p>
 * <p>
 * There are two main operations available, get and put (see start-end transactions), and both
 * expect a {@code Key<Class<?>>} as input. The output is the same type of the key's
 * {@code Class<?>} type parameter. For instance, a call to
 * {@code get(new Key<Spec>(string, Spec.class))} returns a {@code Spec} object if successful, or
 * throws a {@link CommandException} otherwise. There are two main maps for a section manager. One
 * that stores {@link Command} processing objects for a given {@code Class<?>}. That is, each kind
 * of {@code Class<?>} within a key <strong>must</strong> have a corresponding {@code Command}
 * within the map. For instance, for type checking Z we have {@code SectTypeEnvAnn.class} mapped to
 * {@code net.sourceforge.czt.typecheck.z.TypeCheckCommand}. These mappings are according to
 * associated .command files within the session project.
 * </p>
 * <p>
 * The second map is between {@link Key} and its corresponding resource, as calculated by the
 * {@code Key}'s associated command. For instance, when parsing Z we have {@code Key<Spec>} mapped
 * to the underlying {@code Spec} object resulting from the computation of the command. One
 * important distinction to be made is regarding managed and non-managed resources. That is,
 * resources produced within CZT tools and resources used by CZT tools, respectively. The only
 * non-managed resources are mappings for {@code Source} keys: these are usually file or URI
 * resources from external sources. Everything else (so far) is managed by some CZT tool, like
 * specifications by the parser(s), and type environments by the type checker(s).
 * </p>
 * 
 * @author Petra Malik
 * @author Mark Utting
 * @author Leo Freitas
 * @author Andrius Velykis
 */
public class SectionManager
  implements Cloneable, SectionInfo
{
  public static final Dialect DEFAULT_EXTENSION = Dialect.Z;
  public static final boolean DEFAULT_TRACING = false;
  public static final Level DEFAULT_LOGLEVEL = Level.CONFIG;
  public static final Level DEFAULT_TRACELEVEL = Level.FINE;
  public static final Level EXTRA_TRACELEVEL = Level.FINER;

  private Dialect dialect_ = DEFAULT_EXTENSION;
  
  public static final String  SECTION_MANAGER_LIST_PROPERTY_SEPARATOR = File.pathSeparator;
  

  /**
   * The Cache storing computed values (e.g. via commands) for different keys. The contract within
   * section manager ensures that the mappings stored in the cache are Key<T> to T value. Thus we
   * can perform unchecked casts, such as {@code T val = (T) content_.get(Key<T>)}.
   */
  protected final Map<Key<?>, Object> content_ = new HashMap<Key<?>, Object>();

  /**
   * Mapping of relationships from (LHS) Key to the set of other (RHS) keys that depend on it.
   * <p>
   * For example if <blockquote>
   * 
   * <pre>
   * A parents Prelude
   * B parents A
   * C parents B
   * </pre>
   * 
   * </blockquote> We would have a mapping that (excluding {@code Prelude}) <blockquote>
   * 
   * <pre>
   * A -> { B, C }
   * B -> { C }
   * C -> { }
   * </pre>
   * 
   * </blockquote>
   * </p>
   * <p>
   * This way, when removing dependants for {@code A}, we know that {{@code B, C}} and all their
   * dependants need removing. This way, we calculate the transitive closure of dependants. So, if
   * {@code A} is removed then by calculating the transitive closure of dependants we would get that
   * {{@code B, C}} need removing as well.
   * </p>
   */
  protected final Map<Key<?>, Set<Key<?>>> dependants_ = new HashMap<Key<?>, Set<Key<?>>>();

  /**
   * Mapping of relationships from (LHS) Key to the set of other (RHS) keys that it depends on.
   * <p>
   * For the example in {@link #dependants_}, we would get the following map (excluding
   * {@code Prelude}) <blockquote>
   * 
   * <pre>
   * A -> { }
   * B -> { A }
   * C -> { B, A }
   * </pre>
   * 
   * </blockquote>
   * </p>
   */
  protected final Map<Key<?>, Set<Key<?>>> dependencies_ = new HashMap<Key<?>, Set<Key<?>>>();

  /**
   * The default commands. They are those classes capable of computing instances
   * of the resource class that comes from some key.getType().
   */
  private final Map<Class<?>,Command> commands_ = new HashMap<Class<?>,Command>();

  /**
   * Properties are used to store global settings
   * for the commands.
   */
  private final Properties properties_ = new Properties();

  //TODO: make these part of the managed properties?

  /**
   * Determines whether console handling is on or off messages. Trace format
   * is determined by the {@code SimpleFormatter} local class below and
   * it used a {@code ConsoleHandler}. Each FINE trace has a call depth
   * number attached to it. It means how deep in the command computation call
   * it occurred. For instance "SM-UPDATE-2" it means that {@code put}
   * has been called from within two {@code get} contexts.
   */
  private boolean isTracing_ = DEFAULT_TRACING;

  /** Original log level prior to tracing --- it is set back to logger when tracing is off */
  private Level logLevel_ = DEFAULT_LOGLEVEL;
  
  /** Desired tracing level: 
   *    FINE   = just UPDATES      (put); 
   *    FINER  = UPDATE+QUERY      (get/put); 
   *    FINEST = UPDATE+QUERY+CMDS (get/put/cmds.compute);
   *
   *  It presumes commands will follow this logging protocol.
   */
  private Level tracingLevel_ = DEFAULT_TRACELEVEL;

  /**
   * Logger handler used for tracing information to the console.
   */
  private final ConsoleHandler consoleHandler_ = new ConsoleHandler();

  /**
   * The transaction stack contains tracks active transactions. Each transaction also has a number
   * value assigned, which indicates the index in {@link #pendingDeps_}, where the transaction's
   * dependencies start. See {@link #pendingDeps_} for an example.
   * <p>
   * The top of the transaction stack is the currently active transaction.
   * </p>
   */
  /*
   * Invariant: From the stack top downwards, the transaction index must point to a valid element in
   * pendingDeps_. Indexes are ordered within the stack; but might be the same, when there are no
   * dependencies to be considered.
   * 
   * @invariant
   *    forall (k, i) in transactionStack.listIterator().previous() : 
   *            i < pendingDeps_.size() && hasPrevious() --> previous().i <= i
   */
  // for LogBuilder access efficiency; final to ensure no messing around
  protected final Stack<Pair<? extends Key<?>, Integer>> transactionStack_ = 
      new Stack<Pair<? extends Key<?>, Integer>>();
  
  /**
   * The list of pending implicit dependencies, collected via the {@link #get(Key)} calls. Each
   * transaction in the {@link #transactionStack_} reference a particular point in this list. It
   * means that the dependencies of that particular transactions are the ones <strong>above</strong>
   * the index. When the transaction is ended, its dependencies from the pending list will be added
   * to the dependency maps.
   * <p>
   * For example, let the {@link #transactionStack_} be [ (A, 0), (B, 2) ], and
   * {@link #pendingDeps_} be [C, B, D, E]. Then the dependencies of B are {D, E}, and dependencies
   * of A are {C, B, D, E}.
   * </p>
   * TODO The outer transaction collects all the dependencies of inner transactions, but can it be
   * that some of them are not actually dependencies? E.g. during parsing the ThmTable is computed
   * by calling {@code #get(parent, ThmTable)}. This means that the outer transaction (e.g. Sect)
   * would have these ThmTables as dependencies, even though it actually does not depend on them.
   */
  protected final List<Key<?>> pendingDeps_ = new ArrayList<Key<?>>();

  /**
   * The expected transaction for the next {@link #startTransaction(Key)} call. The value is added
   * by {@link #postponeTransaction(Key, Key)}, to indicate what a transaction is postponed
   * (cancelled) in favor of. The next {@link #startTransaction(Key)} call must be of this key, if
   * set.
   * 
   * Note we are using a single value instead of stack because we do not allow multiple postpones.
   * E.g. a postpone follows a {@link #get(Key)}, so additional dependencies would have been added
   * to the parent transaction, violating contract of {@link #postponeTransaction(Key, Key)}.
   */
  private Key<?> expectedPostponeTransaction_ = null;

  private final Set<String> permanentKeys_ = new HashSet<String>();


  /**
   * DESIGN-DECISION: having "default" dialects create problems when trying to resolve default
   * 				  section parent for multi-layered language extensions. In any case, this
   * 				  should be declared from the begingging anyway.
  
  */
  //@Deprecated
  //private SectionManager()
  //{
  //  throw new UnsupportedOperationException("Cannot have a section manager for a unknown dialect");
  //}
  
  /** Creates a new section manager for a given Z extension/dialect.
   *  It calls putCommands(extension) to 
   * @param extension  A Z dialect ("z", "zpatt", "oz", "circus", etc.)
   */
  public SectionManager(Dialect extension)
  {
    this(extension, DEFAULT_TRACING, DEFAULT_LOGLEVEL, DEFAULT_TRACELEVEL);
  }

  public SectionManager(Dialect extension, boolean doTrace, Level logLevel, Level tracingLevel)
  {
    // create a console handler for tracing with simple formatting
    consoleHandler_.setLevel(tracingLevel);
    consoleHandler_.setFormatter(new SimpleFormatter(false, true, false, true));

    // set the section manager logging level at start
    getLogger().setLevel(logLevel);
    getLogger().log(Level.FINEST, "Creating a new {0} section manager", extension);

    isTracing_ = false;
    // initialise the logger's handlers + isTracing_ flag via setTracing();
    setTracing(doTrace, tracingLevel);

    putCommands(extension);
    dialect_ = extension;

    registerDefaultPermanentKeys();
  }

  @Override
  public final Dialect getDialect()
  {
    return dialect_;
  }

  /**
   * Returns a new SectionManager with the same content, commands, and properties.
   * <p>
   * The maps for storing content, commands, and properties are copied, however the content of the
   * maps is <B>not</B> cloned. That is, content can be added to the new section manager without
   * affecting the old one, but destructive changes to its content will show up in this section
   * manager as well.
   * </p>
   * <p>
   * If cloning happens during a transaction, it will only have information from already finished
   * transaction. This includes objects in the section manager, dependencies, etc. The pending
   * transactions and their dependencies, however, are not cloned. Even more, pending transaction
   * keys are removed from the cloned section manager, thus removing everything that may have been
   * depending on the pending transactions (e.g. a LMF is computed before ZSect computation ends, so
   * cloning in the middle of this transaction, will remove the computed LMF for the pending ZSect
   * transaction).
   * </p>
   * 
   * @return A shallow clone of the section manager, minus the pending transactions.
   */
  @Override
  public SectionManager clone()
  {
    // We allow there to be ongoing transactions during the clone. Just make sure it is cleaned
    // appropriately, and pending transactions are removed.
    // assertNoTransactions(null);

    SectionManager result = new SectionManager(dialect_, isTracing_, logLevel_, tracingLevel_);
    result.permanentKeys_.addAll(permanentKeys_);
    copyMap(content_, result.content_);
    copyMap(commands_, result.commands_);
    copyMap(properties_, result.properties_);
    // For dependants/dependencies, we use a deeper cloning - we clone both the maps, and the sets
    // in the maps. So updating dependencies in the clone will not affect the original.
    copyMapSets(dependants_, result.dependants_);
    copyMapSets(dependencies_, result.dependencies_);

    // Don't copy the transaction stack or pending dependencies list.
    // However, remove the currently pending transactions from the cloned section manager,
    // thus removing partially-computed complex objects (e.g. LMF for partially computed ZSect).
    for (Pair<? extends Key<?>, Integer> transaction : transactionStack_) {
      Key<?> transactionKey = transaction.getFirst();
      result.removeKey(transactionKey);
    }

    return result;
  }

  @Override
  public String toString()
  {
    return new LogBuilder("Section manager contains:").content().toString();
  }

  protected final void registerDefaultPermanentKeys()
  {
    for(String k : Section.standardSections())
    {
      permanentKeys_.add(k);
    }
    permanentKeys_.add("cyclic-parse-manager");
  }

  protected boolean registerPermanentKey(String key)
  {
    return permanentKeys_.add(key);
  }

  protected boolean removePermanentKey(String key)
  {
    return permanentKeys_.remove(key);
  }

  //protected boolean isPermanentToolkitKey(Key<?> key)
  //{
    // prelude, zeves_prelude, oz_prelude, circus_prelude, etc
    //return key.getName().indexOf("prelude") == 1 || key.getName().endsWith("_toolkit");
    //return permanentKeys_.contains(key.getName());
  //}

  public boolean isPermanentKey(Key<?> key)
  {
    // cyclic sections management is also permanent
    //return isPermanentToolkitKey(key) || key.getName().equals("cyclic-parse-manager");
    return permanentKeys_.contains(key.getName());
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#reset()
   */
  @Override
  public void reset() throws SectionInfoException
  {
    // don't reset if there are any ongoing transactions
    assertNoTransactions(null);

    getLogger().finest("Resetting section manager key-mapped resources.");
    
    List<Key<?>> removeKeys = new ArrayList<Key<?>>(content_.keySet().size());
    for (Key<?> key : content_.keySet()) {
      if (!isPermanentKey(key))
      {
        // remove non-permanent keys
        removeKeys.add(key);
      }
    }
    for (Key<?> dKey : removeKeys)
    {
      removeKey(dKey);
    }
    if (isTracing_)
    {
      new LogBuilder("Remaining resources").contentKeys().fine();
    }
    
    // reset the expected transaction
    expectedPostponeTransaction_ = null;
    // clear the pending dependencies just in case - though it should be empty, since there are no
    // transactions
    pendingDeps_.clear();
  }

  private static <E,F> void copyMap(Map<E,F> from, Map<E,F> to)
  {
    to.clear();
    to.putAll(from);
  }

  /**
   * Copies a map, which contains value sets. The sets are also cloned - so updating sets in the
   * original map will not affect the result map.
   * 
   * @param from
   * @param to
   */
  private static <E,F> void copyMapSets(Map<? extends E,? extends Set<F>> from, Map<E, Set<F>> to)
  {
    to.clear();
    for (Entry<? extends E,? extends Set<F>> entry : from.entrySet()) {
      to.put(entry.getKey(), entry.getValue() != null ? new HashSet<F>(entry.getValue()) : null);
    }
  }

  /**
   * <p>Returns a property.</p>
   *
   * <p>Properties are used to store global settings
   * for the commands.  For example, the "czt.path" property
   * defines the directory where specifications can be loaded from.</p>
   * @param key property name
   * @return property value
   */
  public String getProperty(String key)
  {
    return properties_.getProperty(key);
  }
  
  public boolean hasProperty(String key)
  {
    return (getProperty(key) != null);
  }

  /**
   * <p>Returns all the current property settings.</p>
   *
   * <p>Properties are used to store global settings
   * for the commands.  For example, the "czt.path" property
   * defines the directory where specifications can be loaded from.</p>
   * 
   * @return the resulting Properties object should be treated as read-only.
   */
  public Properties getProperties()
  {
    return properties_;
  }

  /**
   * Sets a property to the given value.
   *
   * <p>Properties are used to store global settings
   * for the commands.  See getProperty.</p>
   * @param key property key
   * @param value property value
   * @return returns old property value or null if not present before.
   */
  public Object setProperty(String key, String value)
  {
    return properties_.setProperty(key, value);
  }

  /**
   * <p>Sets a whole bunch of properties to the given values.
   * This sets all the properties defined by {@code props}
   * including its default properties (if it has any).</p>
   *
   * <p>Properties are used to store global settings
   * for the commands.  See getProperty.</p>
   * @param props 
   */
  public void setProperties(Properties props)
  {
    Enumeration<?> e = props.propertyNames();
    while (e.hasMoreElements()) {
      String key = (String) e.nextElement();
      properties_.setProperty(key, props.getProperty(key));
    }
  }

    public boolean getBooleanProperty(String propertyKey)
  {
    return "true".equals(getProperty(propertyKey));
  }

  public int getIntegerProperty(String propertyKey)
  {
    int result;
    try
    {
      String value = getProperty(propertyKey);
      if (value == null) { value = ""; }
      result = Integer.parseInt(value);
    }
    catch (NumberFormatException e)
    {
      // silently return 0;?
      //result = 0;
      throw e; // No. Care about it whomever called it.
    }
    return result;
  }

  public List<String> getListProperty(String propertyKey)
  {
    String value = getProperty(propertyKey);
    if (value == null) { value = ""; }
    return Arrays.asList(value.split(SECTION_MANAGER_LIST_PROPERTY_SEPARATOR));
  }


  /**
   * Adds the default commands for the given Z extension/dialect.
   * If extension is "XYZ", it adds all the commands defined in the 
   * "/XYZ.commands" file (see session/src/main/resources).
   * @param extension 
   */
  public final void putCommands(Dialect extension)
  {
    getLogger().log(Level.FINEST, "Set extension to ''{0}''", extension);
    URL url = getClass().getResource("/" + extension.toString() + ".commands");
    if (url != null) {
      putCommands(url);
      return;
    }
    final String message = "Unknown extension " + extension;
    getLogger().warning(message);
  }

  /**
   * Loads a collection of commands from the given properties file/url.
   * See session/src/main/resources for example *.commands XML files.
   * @param url location where to looc for XML-formated list of commands.
   * @throws NullPointerException if url is {@code null}.
   */
  public void putCommands(URL url)
  {
    getLogger().log(Level.FINEST, "Load commands from URL ''{0}''", url);
    final String errorMessage = "Error while loading default commands " +
      "for the section manager: Cannot open " + url.toString();
    try {
      Properties props = new Properties();
      InputStream is = url.openStream();
      try {
        props.loadFromXML(is);
        putCommands(props);
      } finally {
        is.close();
      }
    }
    catch (IOException e) {
      getLogger().warning(errorMessage);
      throw new RuntimeException(errorMessage, e);
    }
  }

  /** Adds a set of default commands from a Properties object.
   * @param props <code>Properties</code> object to get the commands from
   */
  public void putCommands(Properties props)
  {
    for (Map.Entry<Object,Object> entry : props.entrySet()) {
      putCommand((String) entry.getKey(), (String) entry.getValue());
    }
  }

  /** Add a new command for calculating information of a given type.
   * This command will override any existing commands used for
   * calculating this type of information.
   *
   * @param type  the name of a Java class.  This defines the type of object
   *              that this command is expected to compute when it is called.
   * @param commandClassName the name of a subclass of
   *                         net.sourceforge.czt.session.Command.
   * @return if update was successful or not.
   */
  public boolean putCommand(String type, String commandClassName)
  {
    final Logger logger = getLogger();
    try {
      Class<?> typeClass = toClass(type);
      Class<?> commandClass = toClass(commandClassName);
      if (typeClass != null && commandClass != null) {
        Object command = commandClass.newInstance();
        if (command instanceof Command) {
          commands_.put(typeClass, (Command) command);
          logger.log(Level.FINEST, "Set command for {0} to {1}", new Object[]{typeClass.getSimpleName(), command});
          return true;
        }
        final String message = "Cannot instantiate command " +
          commandClassName + "; given class is not a command";
        logger.warning(message);
      }
      else
      {
        final String message = "Cannot instantiate command " +
           (typeClass == null ? " with null type Class for " + type : "") +
           (commandClass == null ? " with null command Class for " + commandClassName : "") +
           ". That means some dependencies could not be found.";
        logger.fine(message);
      }
    }
    catch (ExceptionInInitializerError e) {
      final String message = "Cannot instantiate command " + commandClassName +
        "; exception in initialzier";
      logger.warning(message);
    }
    catch (IllegalAccessException e) {
      final String message = "Cannot instantiate command " + commandClassName +
        "; illegal access exception";
      logger.warning(message);
    }
    catch (InstantiationException e) {
      final String message = "Cannot instantiate command " + commandClassName +
        "; instantiation exception";
      logger.warning(message);
    }
    catch (SecurityException e) {
      final String message = "Cannot instantiate command " + commandClassName +
        "; security exception";
      logger.warning(message);
    }
    return false;
  }

  /**
   * Returns Class.forName(className) but does not throw exceptions.
   * 
   * Exception messages are sent to a logger, so will probably not
   * be visible to users.
   * @param name 
   * 
   * @return null if the requested class could not be loaded.
   */
  private Class<?> toClass(String name)
  {
    try {
      return Class.forName(name);
    }
    catch (ExceptionInInitializerError e) {
      final String message = "Cannot get class " + name +
        "; exception in initialzier";
      getLogger().warning(message);
    }
    catch (LinkageError e) {
      final String message = "Cannot get class " + name +
        "; linkage error";
      getLogger().warning(message);
    }
    catch (ClassNotFoundException e) {
      final String message = "Cannot get class " + name +
        "; class cannot be found";
      getLogger().finest(message);
    }
    return null;
  }

  /**
   * Add a new command for calculating information, overriding any
   * existing commands used for calculating this type of information.
   *
   * @param infoType The type of information the command will calculate.
   * @param command  The command that will calculate the information.
   */
  public void putCommand(Class<?> infoType, Command command)
  {
    commands_.put(infoType, command);
  }

  /**
   * Returns the command for calculating the given type of information.
   * @param infoType type of command
   * @return command for given type
   */
  public Command getCommand(Class<?> infoType)
  {
    return commands_.get(infoType);
  }
  
  public Iterator<Class<?>> getCommandKeys()
  {
    return Collections.unmodifiableSet(commands_.keySet()).iterator();
  }

  /**
   * Checks that there are no transactions at all - throws an exception otherwise.
   * 
   * @param expected
   * @throws SectionInfoException
   *           if transaction stack is not empty
   */
  protected void assertNoTransactions(Key<?> expected) throws SectionInfoException
  {
    if (hasTransaction())
    {
      throw new SectionInfoException(new LogBuilder(
          "There are outstanding transactions").key(expected).transactions().exStr());
    }
  }

  /**
   * Checks that the given {@code key} is not cached in the section manager - throws an exception
   * otherwise.
   * 
   * @param key
   * @throws SectionInfoException
   *           if the {@code key} is cached.
   */
  protected void assertNotCached(Key<?> key) throws SectionInfoException
  {
    if (isCached(key))
    {
      throw new SectionInfoException(new LogBuilder(
          "Key has already been calculated and cached").key(key).exStr());
    }
  }

  /**
   * Checks that there are no existing transaction for the given {@code key} (thus the transaction
   * is new) - throws and exception otherwise.
   * 
   * @param key
   * @throws SectionInfoException
   *           if a transaction exists for the {@code key}
   */
  protected void assertNewTransaction(Key<?> key) throws SectionInfoException
  {
    if (hasTransaction(key))
    {
      throw new SectionInfoException(new LogBuilder(
          "There is an ongoing transaction for the given key").key(key).transactions().exStr());
    }
  }

  /**
   * Checks that the top of transaction stack (the current transaction) is the given {@code key} -
   * throws an exception otherwise.
   * 
   * @param expected
   * @throws SectionInfoException
   *           if there are not transactions at all, or the top of transaction stack is not the
   *           {@code key}.
   */
  protected void assertCurrentTransaction(Key<?> expected) throws SectionInfoException
  {
    Key<?> currentTrans = getCurrentTransaction();
    if (currentTrans == null) {
      throw new SectionInfoException(new LogBuilder(
          "Transaction stack is empty")
         .expected(expected).transactions().exStr());
    }
    
    if (!expected.equals(currentTrans))
    {
      throw new SectionInfoException(new LogBuilder(
          "Transaction stack top is not the one expected")
         .expected(expected).key(currentTrans).transactions().exStr());
    }
  }

  protected boolean hasTransaction()
  {
    return !transactionStack_.isEmpty();
  }

  @Override
  public Set<Key<?>> keysOf(String name)
  {
    Set<Key<?>> result = new HashSet<Key<?>>();
    for (Key<?> k : content_.keySet())
    {
      if (k.getName().equals(name))
      {
        result.add(k);
      }
    }
    return result;
  }

  @Override
  public <T> Set<Key<? extends T>> keysOf(Class<T> clsName)
  {
    Set<Key<? extends T>> result = new HashSet<Key<? extends T>>();
    for (Key<?> k : content_.keySet())
    {
      if (clsName.isAssignableFrom(k.getType()))
      {
        // the above checks that the type of K is a subclass of clsName,
        // so we can safely cast the key generics
        @SuppressWarnings("unchecked")
        Key<? extends T> subtypeKey = (Key<? extends T>) k;
        result.add(subtypeKey);
      }
    }
    return result;
  }

  /**
   * Returns whether the given Key has already been computed
   * and is cached.
   */
  @Override
  public boolean isCached(Key<?> key)
  {
    return content_.get(key) != null;
  }

  /**
   * Returns whether the given value has already been computed
   * and is cached.
   * @param <T> returned key type
   * @param value value to search for key
   * @return value's associated key
   */
  @Override
  public <T> Key<? super T> retrieveKey(T value)
  {
    Key<? super T> result = null;

    // Do a search of all entries containing the requested value
    for (Map.Entry<Key<?>, Object> nextEntry : content_.entrySet())
    {
      Object nextValue = nextEntry.getValue();
      if (nextValue.equals(value))
      {
        /*
         * The #addToCache() contract ensures that content_ maps Key<T> keys to T values. Since 
         * the value can actually be a subclass of T, when doing a backwards search here, we use 
         * Key<? super T> to indicate a correct type cast.
         */
        @SuppressWarnings("unchecked")
        Key<? super T> nextKey = (Key<? super T>) nextEntry.getKey();
        result = nextKey;

        // Note that there is no need to impose any transactional constraints here, if in the middle
        // of a transaction, it would only return the key at that moment, even if the Key-Value will
        // change after the transaction.
        //assertNoOngoingTransactionFor(result);

        break;
      }
    }
    // result != null => isCached(result)
    // result == null || isCached(result)
    assert result == null || isCached(result) :
      "section manager inconsistency: found a key for given value that is not cached.";
    return result;
  }

  private boolean hasTransaction(Key<?> key)
  {
    return hasTransaction(Collections.singleton(key));
  }
  
  private boolean hasTransaction(Collection<? extends Key<?>> keys)
  {
    for(Pair<? extends Key<?>, Integer> p : transactionStack_)
    {
      if (keys.contains(p.getFirst())) {
        return true;
      }
    }
    
    return false;
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#getCurrentTransaction()
   */
  @Override
  public Key<?> getCurrentTransaction()
  {
    if (!transactionStack_.isEmpty()) {
      return transactionStack_.peek().getFirst(); 
    } else {
      return null;
    }
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#put(net.sourceforge.czt.session.Key, java.lang.Object)
   */
  @Override
  public <T> void put(Key<T> key, T value) throws SectionInfoException
  {
    put(key, value, Collections.<Key<?>>emptySet());
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#put(
   *            net.sourceforge.czt.session.Key, java.lang.Object, java.util.Collection)
   */
  @Override
  public <T> void put(Key<T> key, T value, Collection<? extends Key<?>> explicitDependencies)
      throws SectionInfoException
  {
    startTransaction(key);
    endTransaction(key, value, explicitDependencies);
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#ensureTransaction(net.sourceforge.czt.session.Key)
   */
  @Override
  public void ensureTransaction(Key<?> key) throws SectionInfoException
  {
    if (isTracing_)
    {
      new LogBuilder("").transTrace("ENSURE").key(key).caller().fine();
    }
    if (!hasTransaction(key))
    {
      startTransaction(key);
    } else {
      assertCurrentTransaction(key);
    }
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#startTransaction(net.sourceforge.czt.session.Key)
   */
  @Override
  public void startTransaction(Key<?> key) throws SectionInfoException
  {
    if (isTracing_)
    {
      new LogBuilder("").transTrace("START").key(key).caller().fine();
    }

    // check for key duplication
    assertNewTransaction(key);
    assertNotCached(key);

    // if there is an expected transaction (via postpone), check it matches the start key
    if (expectedPostponeTransaction_ != null)
    {
      if (!expectedPostponeTransaction_.equals(key)) {
        throw new SectionInfoException(new LogBuilder(
            "Expected key after a postponed transaction does not match")
           .expected(expectedPostponeTransaction_).key(key).transactions().exStr());
      }
      // reset the expected key - the postpone is fulfilled
      expectedPostponeTransaction_ = null;
    }

    // add the a transaction to the stack, where the dependencies current list state/size
    // determines the pointer where to collect dependencies upon put. Ex: first time it will
    // be empty, hence at index 0. After that, it will one index after the last transactions.
    Pair<? extends Key<?>, Integer> pair = Pair.getPair(key, pendingDeps_.size());
    transactionStack_.push(pair);
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#endTransaction(
   *                    net.sourceforge.czt.session.Key, java.lang.Object)
   */
  @Override
  public <T> void endTransaction(Key<T> key, T value) throws SectionInfoException
  {
    endTransaction(key, value, Collections.<Key<?>>emptySet());
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#endTransaction(
   *            net.sourceforge.czt.session.Key, java.lang.Object, java.util.Collection)
   */
  @Override
  public <T> void endTransaction(Key<T> key, T value, Collection<? extends Key<?>> explicitDependencies) 
      throws SectionInfoException
  {
    if (key == null || value == null || explicitDependencies == null) {
      throw new SectionInfoException(new LogBuilder(
          "Cannot end transaction with null value or explicit dependencies for key").key(key).exStr());
    }
    
    if (isTracing_)
    {
      new LogBuilder("").transTrace("END-ENTRY").key(key).caller().fine();
    }

    // check that the current transaction is being ended
    assertCurrentTransaction(key);
    
    // add explicit dependencies to the pending list
    pendingDeps_.addAll(explicitDependencies);
    
    // remove the transaction from the stack - it is being ended
    Pair<? extends Key<?>, Integer> currentTrans = transactionStack_.pop();
    assert key.equals(currentTrans.getFirst());
    
    // get the pending dependency keys (implicit and explicit) for this transaction
    Set<Key<?>> keyPendingDeps = getPendingDeps(key, currentTrans.getSecond());

    // add the mapping to the cache, as well as create the dependency maps
    addToCache(key, value);
    addDependencies(key, keyPendingDeps);
    
    // if this is the last transaction clear the dependencies list
    clearPendingIfNoTransactions();

    if (isTracing_)
    {
      new LogBuilder("").transTrace(
    		  //(value == null ? "CANCEL": "END") never null?
    		  "END" + "-EXIT")
        .key(key).pendingDeps().transactions(true).caller().fine();
    }
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#cancelTransaction(net.sourceforge.czt.session.Key)
   */
  @Override
  public Set<Key<?>> cancelTransaction(Key<?> key) throws SectionInfoException
  {
    if (key == null) {
      throw new SectionInfoException(new LogBuilder(
          "Cannot cancel transaction with null key").exStr());
    }
    
    // check that the current transaction is being cancelled
    assertCurrentTransaction(key);
    
    if (isTracing_)
    {
      new LogBuilder("").transTrace("CANCEL-ENTRY").key(key).caller().fine();
    }
    
    // check the given transaction is the current one
    assertCurrentTransaction(key);

    // remove the transaction from the stack - it is being cancelled
    Pair<? extends Key<?>, Integer> currentTrans = transactionStack_.pop();
    assert key.equals(currentTrans.getFirst());
    
    // get the implicit pending dependency keys for this transaction
    Set<Key<?>> keyPendingDeps = getPendingDeps(key, currentTrans.getSecond());

    /*
     * Previously we removed the pending keys as well, when cancelling the transaction. However,
     * cancellation just means that something could not be calculated. Now upon this case, the
     * parent transactions may choose to continue. So we still want to keep these dependencies (even
     * though there is a "gap" now), that if something changes in the "cancelled" part - the
     * dependants would be remove and would have to recompute, possibly succeeding in the
     * "cancelled" part now.
     */
    // keyPendingDepsSubList.clear();

    // Only remove keys when non-permanents are cancelled
    // TODO is this correct? If "Prelude" fails and cancels (or is being postponed - thus in the
    // middle of calculation), we would remove its dependants.
    if (!isPermanentKey(key))
    {
      // Chase explicit dependencies that might be added for the cancelling key.
      // For example, LMF depends on ZSect explicitly. So if parsing fails, and ZSect is cancelled,
      // the already-calculated LMF will be removed as well.
      //
      // Note that this will not remove the finished transactions that do not depend on the current
      // one, e.g. parents. So even if we cancel parsing a ZSect, its parents (successfully parsed
      // ZSects) are not removed.
      removeKey(key);
    }
    
    // if this is the last transaction clear the dependencies list
    clearPendingIfNoTransactions();

    if (isTracing_)
    {
      new LogBuilder("").transTrace("CANCEL-EXIT")
        .key(key).pendingDeps().transactions(true).caller().fine();
    }
    
    return keyPendingDeps;
  }
  
  private void cancelUpToTransaction(Key<?> key) throws SectionInfoException
  {
    // Go backwards and cancel all transactions up to the key
    while (hasTransaction(key))
    {
      // while the transaction exists, cancel the current transaction
      Key<?> currentTrans = getCurrentTransaction();
      cancelTransaction(currentTrans);
    }
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#postponeTransaction(
   *            net.sourceforge.czt.session.Key, net.sourceforge.czt.session.Key)
   */
  @Override
  public void postponeTransaction(Key<?> postponeKey, Key<?> nextKey) 
      throws SectionInfoException
  {
    if (nextKey == null) {
      throw new SectionInfoException(new LogBuilder(
          "Key expected for the next transaction cannot be null").exStr());
    }

    if (isTracing_)
    {
      new LogBuilder("").transTrace("POSTPONE").key(nextKey).caller().fine();
    }

    // next key cannot have already been cached
    assertNewTransaction(nextKey);
    assertNotCached(nextKey);
    
    if (expectedPostponeTransaction_ != null)
    {
      // we do not allow postponing after a postponed transaction
      throw new SectionInfoException(new LogBuilder(
          "There already is an expected transaction - cannot postpone again")
         .key(nextKey).expected(expectedPostponeTransaction_).transactions().exStr());
    }

    Set<Key<?>> cancelledDeps = cancelTransaction(postponeKey);
    if (!cancelledDeps.isEmpty()) {
      // There are keys already marked as transaction's dependencies.
      // The postpone should only happen as the immediate action in the command,
      // thus no keys can be marked as dependencies for this transaction.
      throw new SectionInfoException(new LogBuilder(
          "Postponing a transaction with dependencies - only " +
          "fresh transactions (no dependencies) can be postponed")
         .key(postponeKey).expected(nextKey).col("Dependencies", cancelledDeps).transactions().exStr());
    }

    expectedPostponeTransaction_ = nextKey;
  }

  /**
   * Adds a (key, value) mapping to the section manager cache.
   * 
   * @param <T>
   *          Resource key type
   * @param key
   *          Resource key
   * @param value
   *          Value (resource) to associate with given key
   * @throws SectionInfoException
   */
  private <T> void addToCache(Key<T> key, T value) throws SectionInfoException
  {
    assert key != null;
    assert value != null;

    // check key / value pairs are consistent
    if (!key.getType().isInstance(value))
    {
      throw new SectionInfoException(new LogBuilder(
          "Section manager inconsistency: given value type is not an instance of the associated key")
         .str("Key type", key.getType().getName()).str("Value type", value.getClass().getName()).exStr());
    }

    if (content_.containsKey(key))
    {
      throw new SectionInfoException(new LogBuilder(
          "Adding a duplicate key - value for this key is already cached").key(key).exStr());
    }

    // put to the cache
    content_.put(key, value);
    
    if (isTracing_ && !isPermanentKey(key))
    {
      new LogBuilder("").transTrace("UPDATE").key(key).caller().fine();
    }
  }
  
  /**
   * Adds the dependencies (implicit + explicit) for the key to the section manager. The
   * dependencies are iterated to create the two maps of dependants (what depends on the key) and
   * dependencies (what the key depends on).
   * 
   * @param key
   *          resource key
   * @param deps
   * @throws SectionInfoException
   */
  private void addDependencies(Key<?> key, Set<Key<?>> deps) throws SectionInfoException
  {
    assert key != null && deps != null;

    if (isTracing_)
    {
      new LogBuilder("SM-GIVEN-DEPENDENCIES_"+callCnt_)
            .key(key).col("Pending deps", deps).caller().fine();
    }

    /*
     * For each key in the dependency set, mark the given key as a dependant. We mark that the key
     * depends on each key in the {@code deps} set
     */
    // key   = C
    // deps  = A, B
    // build = A -> { C }; B -> { C }
    for(Key<?> dk : deps)
    {
      Set<Key<?>> keyDependants = dependants_.get(dk);
      if (keyDependants == null)
      {
        keyDependants = new HashSet<Key<?>>();
        dependants_.put(dk, keyDependants);
      }
      keyDependants.add(key);
    }

    /*
     * Mark the given dependencies for the key.
     */
    // key   = C
    // deps  = A, B
    // build = C -> { A, B }
    // There can be no dependencies for a new key. If there are, they are not correctly cleaned up
    // from previous runs.
    Set<Key<?>> depKeys = dependencies_.get(key);
    assert depKeys == null || depKeys.isEmpty() : 
       new LogBuilder("Dependencies not empty").key(key).col("Deps", depKeys).toString();
    
    dependencies_.put(key, new HashSet<Key<?>>(deps));

    if (isTracing_)
    {
      new LogBuilder("SM-CALC-DEPENDENCIES_"+callCnt_)
            .key(key).dependants().dependencies().caller().fine();
    }
  }
  
  private Set<Key<?>> getPendingDeps(Key<?> key, Integer pendingIndex) {
    
    // check the pending dependencies index is within range
    if (pendingIndex > pendingDeps_.size())
    {
      throw new SectionInfoException(new LogBuilder(
          "Dependencies index (" + pendingIndex + ") out of bounds for transaction.")
         .key(key).transactions(true).pendingDeps().exStr());
    }
    
    // the keys involved in the dependency on the key
    return new HashSet<Key<?>>(pendingDeps_.subList(pendingIndex, pendingDeps_.size()));
  }
  
  private void clearPendingIfNoTransactions() {
    if (!hasTransaction()) {
      pendingDeps_.clear();
    }
  }
  
  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#removeKey(net.sourceforge.czt.session.Key)
   */
  @Override
  public boolean removeKey(Key<?> key) throws SectionInfoException
  {
    if (isTracing_)
    {
      new LogBuilder("").transTrace("REMOVE-KEY")
            .key(key).dependants().dependencies().caller().fine();
    }

    /*
     * Removal of existing transaction keys is not allowed - check that the given key is not in a
     * transaction. If this assertion fails, it may signal bad transactional structure, or that the
     * dependencies were not properly cleaned up (e.g. there are some old dependants on the removed
     * key, which in turn triggered removal of existing transaction.
     */
    assertNewTransaction(key);

    // remove dependants / dependencies
    removeDependants(key);
    removeDependencies(key);

    // remove contents
    Object old = content_.remove(key);
    return old != null;
  }

  /**
   * Transitively removes the key dependants. For each key that depends on the given {@code key},
   * remove it from the section manager - it will trigger removal of its dependants transitively.
   * 
   * @param key
   * @throws SectionInfoException
   */
  private void removeDependants(Key<?> key) throws SectionInfoException
  {
    // When removing dependants, first remove the mapping, otherwise the recursive removal may loop
    // if there are cyclic dependencies
    Set<Key<?>> keyDependants = dependants_.remove(key);
    if (keyDependants != null)
    {
      for(Key<?> dkey : keyDependants)
      {
        removeKey(dkey);
      }
    }
  }

  /**
   * Removes dependencies mapping of the key - what the key depends on. It does not remove the
   * dependency values from section manager, just the dependency mapping. Furthermore, in each of
   * the dependencies, the method makes sure that the given {@code key} is no longer among their
   * <em>dependants</em>.
   * 
   * @param key
   * @throws SectionInfoException
   */
  private void removeDependencies(Key<?> key) throws SectionInfoException
  {
    // remove the dependency mapping
    Set<Key<?>> keyDependencies = dependencies_.remove(key);
    // go through each dependency, and remove this key from their dependants list
    // this is required, because dependencies may change between computations, so we need
    // a full cleanup, otherwise the next computation may not depend on the depcy, but
    // removal of depcy will trigger removal of the key.
    if (keyDependencies != null) {
      for (Key<?> depcy : keyDependencies) {
        
        Set<Key<?>> keyDependants = dependants_.get(depcy);
        if (keyDependants != null)
        {
          keyDependants.remove(key);
        }
      }
    }
  }

  
  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#getDependants(net.sourceforge.czt.session.Key)
   */
  @Override
  public Set<Key<?>> getDependants(Key<?> key)
  {
    // TODO add pending dependants if the key is in transaction stack?
    // This would be useful if the method is queried during a transaction.
    
    Set<Key<?>> result = dependants_.get(key);
    return result == null ? Collections.<Key<?>>emptySet() : Collections.unmodifiableSet(result);
  }

  
  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.session.SectionInfo#getDependencies(net.sourceforge.czt.session.Key)
   */
  @Override
  public Set<Key<?>> getDependencies(Key<?> key)
  {
    // TODO add pending dependencies if the key is in transaction stack?
    // This would be useful if the method is queried during a transaction.
    
    Set<Key<?>> result = dependencies_.get(key);
    return result == null ? Collections.<Key<?>>emptySet() : Collections.unmodifiableSet(result);
  }

  /**
   * <p>
   * Lookup a key in the section manager. It will never return <code>null</code>.
   * That means, it calculates with the command associated with the key type, the
   * resulting value for that key. If it is already present (i.e., {@link #isCached(Key)} is true),
   * then no further calculation is needed. 
   * </p>
   * <p>
   * See {@link SectionInfo#get(Key)} for the "big picture" description of this method,
   * and for the information about transactions/dependencies.
   * </p>
   * <p>
   * Each extension may install different commands to process each type of key.
   * Having this dynamic scheme minimises the source code dependencies the section manager has.
   * The default commands can be found in the .commands files within the czt.jar.
   * For instance, for the (default) Z extension, the mapping and the lookup
   * algorithm is defined below. For each item we add the tool that (usually) 
   * performs the corresponding algorithm. Obviously, each extension has its own
   * version of some of these commands (see extension corresponding .commands file).
   * 
   * <dl>
   *  <dt>Source location (section management)</dt>
   *      <dd>
   *      For Z, there are five types of CZT sources. A CZT source enables
   *      the section manager commands to find the appropriate resource. 
   *      They key name is the resource name, which may be irrelevant for
   *      certain sources, whereas the key type is <code>Source.class</code>.
   *      The associations for each kind of <code>Source</code> are detailed below.
   *        <dl>
   *          <dl>FileSource</dl>
   *              <dd>   
   *              The algorithm looks for the file resource on the underlying
   *              filesystem according to the file name, which is the resource name. 
   *              Usual code is like:
   *              <br>
   *              <code>FileSource fs = new FileSource("./foo.tex");</code>
   *              </dd>
   *          <dl>UrlSource</dl>
   *              <dd>   
   *              The algorithm follows Java's URI protocols to find resources
   *              over the network or local file system. Resource name is the URI.
   *              </dd>
   *          <dl>StringSource</dl>
   *              <dd>   
   *              Just a placeholder for the resource as a string. 
   *              Resource name is fixed as "StringSource".
   *              </dd>
   *          <dl>StdInSource</dl>
   *              <dd>   
   *              Just a placeholder for the resource from the standard input.
   *              Resource name is fixed as "System.in".
   *              </dd>
   *        </dl>
   *      <br>
   *      Source location is important to tell the give parser(s) the right 
   *      location of various resources. The usual code for that is mainly 
   *      used by the parser(s) and looks like:
   *      <br>
   *      <code>
   *      // For file resource location...
   *      String filename = "./foo.tex"; 
   *      Source source = manager.get(new Key&lt;Source&gt;(name, Source.class));
   *      Term term = ParseUtils.parse(source, manager);
   *      </code>
   *      See {@link SourceLocator} for details.
   *      </dd>
   *  <dt><code>Term</code> parsing (parser)</dt>
   *      <dd>
   *      For Z, there are three types of terms that can parsed using the
   *      section manager: Spec, ZSect, and Term. We detail them below.
   *      For Spec, the key name is the source name to find the specification.
   *      For other terms, the key name is the Z section name to find the term.
   *      The coomand looks up the resource using the key's name.
   *      The algorithm for each kind of <code>Term</code> are detailed below.  
   *        <dl>
   *          <dt>Spec parsing</dt>
   *            <dd>
   *            If the specification has already been parsed through other means,
   *            all of its Z sections are cached in the section manager as well.
   *            Otherwise, the top-level parsing occurs and the resulting spec is cached.
   *            </dd>
   *          <dt>ZSect parsing</dt>
   *            <dd>
   *            If the specification has already been parsed through other means,
   *            all of its Z sections are cached in the section manager as well.
   *            Otherwise, the top-level parsing occurs and the resulting spec is cached.
   *            </dd>
   *          <dt>Term parsing</dt>
   *            <dd>
   *            General terms are wrapped up up to the Z section level, then they
   *            are parsed, and unwrapped back to their right position (i.e., pred, expr, para).
   *            These are usually given through String our StdIn source. They are
   *            useful in tools that require on-the-fly parsing, like theorem provers.
   *            </dd>
   *        </dl>
   *      Parsing errors are collected in the ParseException, which is processed
   *      by a different command detailed below. The parser guarantees the specification 
   *      is syntactically consistent with the correspondant language grammar.
   *      See parser's ParseUtils for details.
   *      </dd>
   *  <dt>Parsing exceptions (parser)</dt>
   *      <dd>
   *      If upon parsing errors are found, the command with a key for <code>ParseException</code>
   *      returns the <code>ParseException</code> containing a list of <code>CztError</code>. One
   *      rarely needs to directly use this, unless creating a top-level tool using the parser,
   *      such as ZLive. The key name must contain the corresponding Source name.
   *      </dd>
   *  <dt>LaTeX markup directives table (parser)</dt>
   *      <dd>
   *      A key with <code>LatexMarkupFunction</code> and a section name returns the
   *      table containing all the LaTeX markup directive information of a parsed 
   *      specification. That includes information about the directive type (i.e., infix,
   *      posfix, prefix, nofix), its LaTeX and Unicode markup, the section where it belongs,
   *      and so on.
   *      </dd>
   *  <dt>Operator templates table (parser)</dt>
   *      <dd>
   *      A key with <code>OpTable</code> and a section name returns the
   *      table containing all the operator template information of a parsed specification.
   *      That includes the section where the operator belongs, its associativity, 
   *      binding power, operator type, its underlying OpTempPara, and so on.
   *      </dd>
   *  <dt>Definitions table (parser)</dt>
   *      <dd>
   *      <p>
   *      A key with <code>DefinitionTable</code> and a section name returns the
   *      table containing all the information about declared types of definitions
   *      of a parsed specification. That includes the section where the definition
   *      appears, as well as its generic types, name and declared expression.
   *      </p>
   *      <p>
   *      Note that the typechecker returns the carrier set for every name, whereas
   *      the definition table returns the declared (non-maximal) type. It is 
   *      recommended that one only use definition tables of typechecked sections
   *      in order to avoid problems with overloaded names in schemas with type 
   *      incompatible carrier sets, for instance.
   *      </p>
   *      </dd> 
   *  <dt>Jokers table (parser)</dt>
   *      <dd>
   *      Calculates the table of wildcard names used by the term rewriting modules.
   *      See zpatt extension, Rules and ZLive projects for more details.
   *      </dd>
   *  <dt>Pretty printing (printer)</dt>
   *      <dd>
   *      The pretty printer can be called with keys typed with one of the various 
   *      subclasses of <code>CztPrintString</code> class and named with the Z section 
   *      to print, or filename without path or extension for specifications. 
   *      For Standard Z, there are four possible options for pretty printing:
   *      <ol> 
   *        <li>Standard Z LaTeX printing with <code>LatexString</code> typed keys;</li>
   *        <li>Spivey's Z LaTeX printing with <code>OldLatexString</code> typed keys;</li>
   *        <li>Unicode printing (UTF8 or UTF16) with <code>UnicodeString</code> typed keys;</li>
   *        <li>ZML (Z in XML) printing (UTF8) with <code>XMLString</code> typed keys.</li>
   *      </ol>
   *      The pretty-printer guarantees the specification is syntactically consistent with 
   *      the correspondant language printing grammar. See printer's PrintUtils for details.
   *      </dd>   
   *  <dt>Type environments (typechecker)</dt>
   *      <dd>
   *      Keys typed with <code>SectTypeEnv</code> and named with a Z section name 
   *      return a <code>SectTypeEnv</code>, which contains a list of <code>NameSectTypeTriple</code>
   *      containing a triple formed by the section name, the declared name, and its
   *      carrier set type. The typechecker guarantees the specification is syntactically type-consistent.
   *      Note that to typecheck specifications, one needs to typecheck
   *      (manually) each one of its ZSect lements. See typechecker's TypeCheckUtils for details.
   *      </dd>
   *  <dt>Domain check environments (domainchecker)</dt>
   *      <dd>
   *      Keys typed with one of the two possible domain check environments and named
   *      according to the rules for source location of each of the possible terms can be used.
   *        <ul>
   *           <li><code>Spec</code> terms generate <code>SpecDCEnvAnn</code>, 
   *                which contains a list of <code>ZSectDCEnvAnn</code> for each
   *                ZSect it contains, and the name that can be used to locate the
   *                enviroment original resource's (i.e., Spec filename without extension).
   *                It is also possible to retrieve a <code>Spec</code>
   *                containing <code>ZSect</code> with a list of conjectures for the 
   *                correspondent <code>ZSect</code> where they were originated.
   *           </li>
   *           <li><code>ZSect</code> terms generate <code>ZSectDCEnvAnn</code>,
   *               which contain  a list of pairs containing each <code>ZSect</code>
   *               <code>Para</code> that generates a corresponding <code>Pred</code>
   *               domain check verification condition, and the original Z section name.
   *                It is also possible to retrieve a <code>ZSect</code>
   *                containing a list of conjectures for the correspondent <code>ZSect</code> 
   *                where they were originated.
   *           </li>
   *        <ul>
   *      The domain checker calculates, for each ZSect paragraph, semantic-consistency
   *      conjectures ensuring there is a denoting model for the underlying specification.
   *      In other words, partial functions are applied within their domains and definite
   *      description denote a unique value. See domainchecker's DomainCheckUtils for details.
   *      </dd>
   * </dl>   
   * The general rule is that the key's type determine which command to perform,
   * whereas the key's name determine how the resource is to be found. As mentioned
   * above some commands use the results of other commands while being performed.
   * For instance, parsing Spec uses source location with a given file name, whereas
   * parsing a Z section uses source location with a given Z section name. Therefore, 
   * to parse a Spec, one needs to give a file name, whereas to parser a Z section,
   * one need to give the Z section name. Note that this means the Z section name
   * must be the same as the underlying resource, which if FileSource, means the 
   * Z section file must be named the same as the Z section itself.
   * </p>
   * <p>
   * For other extensions the lookup is similar, except that different 
   * classes get associated with each one of these commands. Furthermore,
   * new commands may be added or dynamically modified at any time. This
   * way both the user or a developer may change the stub used to compute
   * each available lookup functionality. 
   * </p>
   * <p>
   * Finally, as the lookup operation may involve the recursive execution of
   * several commands, the underlying section manager cache will observe
   * intermediate side-effects whilst performing a top-level command by the user.
   * These results are cached/permanent until the SectionManager is {@link #reset()}.
   * </p>
   *
   * @param <T> type of key
   * @param key   The key to be looked up.
   * @return      An instance of key.getType().
   * @throws      CommandException if the lookup was unseccessful.
   * @throws      SectionInfoException if the transactions for computation fail.
   * @see SectionInfo#get(Key)
   */
  @Override
  public <T> T get(final Key<T> key) throws CommandException, SectionInfoException
  {
    if (isTracing_ && !isPermanentKey(key))
    {
      new LogBuilder("SM-QUERY -ENTRY-"+callCnt_).key(key).caller().finer();
      // enter a request context
      callCnt_++;
    }

    // add the dependency key at this level - implicit dependencies within current transaction, if any
    // (e.g., avoid tracking keys when there are no pending transactions).
    if (hasTransaction())
    {
      pendingDeps_.add(key);
    }

    final Class<T> infoType = key.getType();
    final String name = key.getName();
    boolean cached = true;
    
    // the #addToCache() method ensures that content_ maps Key<T> keys to T values
    @SuppressWarnings("unchecked")
    T result = (T) content_.get(key);
    if (result == null)
    {
      cached = false;
      Command command = commands_.get(infoType);
      if (command == null)
      {
        throw new UnknownCommandException(dialect_, "No command available to compute " + key);
      }
      // starts a transaction for the given key if not cached
      startTransaction(key);
      // make the actual request
      try
      {
        // The command result flag is not used anywhere at the moment, and is only there
        // for possible future API needs.
        @SuppressWarnings("unused")
        boolean cres = command.compute(name, this);
      }
      catch (CommandException e)
      {
        /**
         * If the command computation throws an exception, cancel the transaction that has been
         * started before the computation. This is the default case, when the command only handles
         * the ending of transaction.
         * <p>
         * For complex cases, e.g. when postponing is involved, the command may have cancelled the
         * started transaction manually. In that case, we need to check whether the transaction
         * still exists - and cancel it only then.
         * </p>
         * <p>
         * This implementation is also very conservative, and catches all exceptions (see below).
         * Even more, it tries to cancel the transaction even if it is not the current one. For
         * example, if there is an error in the command implementation, and it manually starts
         * additional transactions, exceptions for which are not handled properly. Then when an
         * exception is thrown, there may be more than one outstanding transaction since starting it
         * before the computation above. The handler will cancel all transactions from the top up to
         * the {@code key}.
         * </p>
         */
        cancelUpToTransaction(key);
        throw e;
      }
      catch (RuntimeException re)
      {
        // be conservative and catch runtime exceptions as well to cleanup the transactions
        cancelUpToTransaction(key);
        throw re;
      }
      
      // the #addToCache() method ensures that content_ maps Key<T> keys to T values
      @SuppressWarnings("unchecked")
      T commandResult = (T) content_.get(key);
      
      if (commandResult == null)
      {
        final String message = "Key " + key + " not computed by " + command;
        throw new CommandException(dialect_, message);
      }
      
      result = commandResult;
    }
    //never null here, assert result != null : "Section manager computed null result!";

    if (isTracing_ && !isPermanentKey(key))
    {
      // close the context
      callCnt_--;
      // log SM query results
      new LogBuilder("SM-QUERY -EXIT-"+callCnt_).key(key).str("Result", result.getClass().getName())
            .pendingDeps().str("Cached", String.valueOf(cached)).finer();
    }
    return result;
  }

  private int callCnt_ = 0;

  private String whoWasCalling(int extraCallDepth)
  {
    Throwable t = new Throwable();
    t.fillInStackTrace();
    StackTraceElement[] stes = t.getStackTrace();
    
    int targetDepth = 2 + extraCallDepth;
    
    if (targetDepth >= 0 && targetDepth < stes.length)
    {
      StackTraceElement el = stes[targetDepth];
      final String msg = el.getClassName() + "." + el.getMethodName() + ", " + el.getLineNumber();
      return msg;
    }
    return "?? who is calling ??";
  }

  public final Logger getLogger()
  {
    return Logger.getLogger(getClass().getName());
  }

  @Override
  public Level getTracingLevel()
  {
    return tracingLevel_;
  }

  @Override
  public boolean isTracing()
  {
    return isTracing_;
  }

  /**
   * Set section management tracing on/off. The SectionManager uses a ConsoleHandler
   * for logging with Level.FINE, which is the one implemented at get/put. Command
   * implementations should use Level.FINER to avoid too verbose outputs. It is
   * important to note that when tracing with the console, both the Logger and the
   * Handler must have their levels set (e.g., the Logger's level overrides the Handler's).
   *
   * @return the previous value of tracing flag
   */
  @Override
  public final boolean setTracing(boolean on, Level level)
  {
    return setTracing(on, consoleHandler_, level);
  }

  public final boolean setTracing(boolean on)
  {
    return setTracing(on, tracingLevel_);
  }

  public boolean setTracing(boolean on, Handler handler, Level level)
  {
    Logger log = getLogger();
    boolean result = isTracing_;
    isTracing_ = on;
    tracingLevel_ = level;
    if (isTracing_)
    {
      handler.setLevel(level);
      log.addHandler(handler);
      logLevel_ = log.getLevel();
      log.setLevel(tracingLevel_);
    }
    else
    {
      log.removeHandler(handler);
      log.setLevel(logLevel_);
    }
    return result;
  }

  public static void traceLog(String msg)
  {
    Logger.getLogger(SectionManager.class.getName()).finest(msg);
  }

  public static void traceConfig(String msg)
  {
    Logger.getLogger(SectionManager.class.getName()).config(msg);
  }

  public static void traceWarning(String msg)
  {
    Logger.getLogger(SectionManager.class.getName()).warning(msg);
  }

  public static void traceInfo(String msg)
  {
    Logger.getLogger(SectionManager.class.getName()).info(msg);
  }
  

  /**
   * A log builder class, which can construct nicely formatted information output about the section
   * manager. Allows to simplify collecting output text for tracing/exception handling.
   * 
   * @author Andrius Velykis
   */
  private class LogBuilder
  {

    private int valIdent = 15;

    private StringBuilder out = new StringBuilder();

    public LogBuilder(String title)
    {
      out.append(title);
    }
    
    public LogBuilder transTrace(String transactionPhase) {
      out.append("SM-" + transactionPhase + "-TRANSACTION-T"+ (transactionStack_.size()+1));
      return this;
    }

    private void tabbedLine(String label, String value, int tabCount)
    {
      out.append("\n");
      for (int index = 0; index < tabCount; index++) {
        out.append("\t");
      }

      out.append(label);

      for (int index = label.length(); index < valIdent; index++) {
        // add dots to the ident
        out.append(".");
      }

      out.append(": ");
      out.append(value);
    }

    private void tabbedLine(String label, String value)
    {
      tabbedLine(label, value, 1);
    }
    
    private String newLineCollection(Collection<?> col, int tabIdent)
    {
      StringBuilder colOut = new StringBuilder();
      
      StringBuilder tabIdentBuilder = new StringBuilder("\n");
      for (int index = 0; index < tabIdent; index++) {
        tabIdentBuilder.append("\t");
      }
      String tabIdentStr = tabIdentBuilder.toString();

      String delim = "";
      for (Object val : col) {
        colOut.append(delim);
        
        String valStr;
        if (col instanceof Key<?>) {
          valStr = keyStr((Key<?>) col);
        } else {
          valStr = String.valueOf(val);
        }
        
        colOut.append(valStr);
        // ident to differentiate from tabbedLine
        delim = tabIdentStr;
      }

      return colOut.toString();
    }

    private String newLineCollection(Collection<?> col)
    {
      return newLineCollection(col, 2);
    }
    
    private String newLineMap(Map<Key<?>, Set<Key<?>>> map) {
      List<String> entries = new ArrayList<String>();
      for (Entry<Key<?>, Set<Key<?>>> entry : map.entrySet()) {
        entries.add(keyStr(entry.getKey()) + "=" + newLineCollection(entry.getValue(), 3));
      }
      
      return newLineCollection(entries);
    }

    private String keyStr(Key<?> key)
    {
      return "(" + key.getName() + "," + key.getType().getSimpleName() + ")";
    }

    public LogBuilder key(Key<?> key)
    {
      if (key != null) {
        tabbedLine("Key", keyStr(key));
      }
      return this;
    }
    
    public LogBuilder expected(Key<?> key)
    {
      if (key != null) {
        tabbedLine("Key expected", keyStr(key));
      }
      return this;
    }

    public LogBuilder transactions(boolean withNums)
    {

      List<String> trStrings = new ArrayList<String>(transactionStack_.size());
      for (Pair<? extends Key<?>, Integer> entry : transactionStack_) {
        String str = keyStr(entry.getFirst());
        if (withNums) {
          str = String.valueOf(entry.getSecond()) + ": " + str;
        }
        trStrings.add(str);
      }

      tabbedLine("Transactions", newLineCollection(trStrings));
      return this;
    }

    public LogBuilder transactions()
    {
      return transactions(false);
    }
    
    public LogBuilder pendingDeps()
    {
      tabbedLine("Pending deps", newLineCollection(pendingDeps_));
      return this;
    }
    
    public LogBuilder contentKeys()
    {
      tabbedLine("Cached", newLineCollection(content_.keySet()));
      return this;
    }
    
    public LogBuilder content()
    {
      
      List<String> entries = new ArrayList<String>();
      for (Entry<Key<?>, Object> entry : content_.entrySet()) {
        entries.add(keyStr(entry.getKey()) + "=" + String.valueOf(entry.getValue()));
      }
      
      tabbedLine("Cached", newLineCollection(entries));
      return this;
    }
    
    public LogBuilder dependants()
    {
      tabbedLine("Dependants", newLineMap(dependants_));
      return this;
    }
    
    public LogBuilder dependencies()
    {
      tabbedLine("Dependencies", newLineMap(dependencies_));
      return this;
    }
    
    public LogBuilder col(String label, Collection<?> col)
    {
      tabbedLine(label, newLineCollection(col));
      return this;
    }
    
    public LogBuilder str(String label, String val)
    {
      tabbedLine(label, val);
      return this;
    }
    
    public LogBuilder caller() {
      tabbedLine("Caller", whoWasCalling(2));
      return this;
    }
    
    @Override
    public String toString()
    {
      return out.toString();
    }

    public String exStr()
    {
      // first print as warning, and then return the "exception string"
      warning();
      return toString();
    }
    
    public void warning() {
      getLogger().warning(toString());
    }
    
    public void fine() {
      getLogger().fine(toString() + "\n");
    }
    
    public void finer() {
      getLogger().finer(toString() + "\n");
    }
    
  }
}
