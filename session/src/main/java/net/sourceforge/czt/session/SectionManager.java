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
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.Stack;
import java.util.logging.ConsoleHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import net.sourceforge.czt.util.Pair;

/**
 * <p>
 * This class is a repository for information about (Z) specs/sections (and its extensions).
 * It stores all the objects used during CZT processing, such as parsed ASTs (abstract syntax trees)
 * type environments, and so on. It provides several services, depending on the
 * kind of key requested. For instance, it can compute the operator table
 * or the LaTeX markup function for a given section, or typecheck or domain check
 * a given Term/Spec/ZSect. The keys to access an object within the section
 * manager are a (Name,Class) pair, which means that several different kinds
 * of objects can be associated with the same name.
 * </p>
 * <p>
 * One of the main goals of this class is to cache commonly used
 * objects, such as the parsed ASTs of toolkit sections, so that they
 * do not have to be repeatedly processed.  This can give great performance
 * improvements. For instance, we envisage one section manager per project, where a
 * project is a collection of files representing sections (e.g., an IDE project like in Netbeans/Eclipse).
 * </p>
 * <p>
 * Nevertheless, a fundamental problem is that data can become
 * inconsistent if you add a section XYZ, then add other sections that
 * uses it (e.g., depend on XYZ). If XYZ changes, it <bf>must</bf> be invalidated within
 * the section manager and have its new version reloaded. Its dependant information must also
 * be reloaded (e.g., everything it is a parent of; or other data computed that depends on it).
 * </p>
 * <p>
 * Our current solution is to have transactions that compute implicit dependencies whilst computing
 * information, as well as explicit (extra) dependencies given by the user. This dependency calculation
 * is quite hard to get right and this is an experimental feature at the moment. That is, the safest
 * choice is to keep fresh(er) section managers if that is of concern (i.e., have section managers
 * per file/buffer rather than projects) greater than performance gains.
 * </p>
 * <p>
 * We track duplicate objects as well as transaction scopes raising SectionManagerException at appropriate places.
 * We are still experimenting with the best approach. The section manager also contain tracing methods to enable
 * better debugging: tracing data is added to the console or Logger handler in order to output all information
 * stored during transaction processing.
 * </p>
 * <p>
 * There are currently three ways of getting/reusing a section manager object.
 * <ol>
 *   <li> <code>new SectionManager()</code>
 *      -- which starts with an empty cache, so gives you the overhead
 *         of parsing toolkits again.</li>
 *   <li> <code>oldSectMan.reset()</code> -- this clears everything in the
 *        cache, except for the prelude and any sections called *_toolkit.</li>
 *   <li> <code>oldSectMan.clone()</code> -- depending upon WHEN you do
 *        this clone, you can decide just how much you want to leave in
 *        the cache.</li>
 * </ol>
 * To avoid reparsing toolkits repeatedly (which makes things slow!),
 * you should avoid creating new section managers and use the reset or
 * clone methods instead. Moreover, you can pass the Z dialect the section
 * manager is responsible for. That (dynamically) determines (via class loading at run time)
 * what tools will be used for parsing, typechecking, etc.
 * </p>
 *
 * <p>As well as the main cache of specification-related objects,
 * this class maintains several other kinds of information, including:
 * <ul>
 *   <li>a <em>properties</em> map that stores a string value for various
 *   property keys (see getProperty and setProperty)</li>
 *   <li>a <em>command</em> map that stores a Command object for each kind of
 *   specification-related type of interest.  These Command objects are
 *   called when the section manager needs to calculate a given type of
 *   object key and it is not already in the cache (see putCommand).</li>
 * </ul>
 * </p>
 * <p>
 * There are two main operations available, get and put, and both expect a <code>Key&lt;Class&lt;?&gt;&gt;</code>
 * as input. The output is the same type of the key's <code>Class&lt;?&gt;</code> type parameter. For instance,
 * a call to <code>get(new Key&lt;Spec&gt;(string, Spec.class))</code> returns a <code>Spec</code> object if
 * successful, or throw a <code>CommandException</code> otherwise.
 * There are two main maps for a section manager. One that stores <code>Command</code>
 * processing objects for a given <code>Class&lt;?&gt;</code>. That is, each kind of <code>Class&lt;?&gt;</code>
 * within a key <bf>must</bf> have a corresponding <code>Command</code> within the map.
 * For instance, for type checking Z we have <code>SectTypeEnvAnn.class</code> mapped to
 * <codenet.sourceforge.czt.typecheck.z.TypeCheckCommand</code>. These mappings are according
 * to associated .command files within the session project.
 * </p>
 * <p>
 * The second map is between <code>Key</code> and its corresponding resource, as calculated
 * by the Key's associated command. For instance, when parsing Z we have <code>Key&lt;Spec&gt;</code>
 * mapped to the underlying <code>Spec</code> object resulting from the computation of the command.
 * One important distinction to be made is regarding managed and non-managed resources. That is,
 * resources produced within CZT tools and resources used by CZT tools, respectively. The only
 * non-managed resources are mappings for <code>Source</code> keys: these are usually file or
 * URI resources from external sources. Everything else (so far) is managed by some CZT tool,
 * like specifications by the parser(s), and type environments by the type checker(s).
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
  public static final String DEFAULT_EXTENSION = "z";
  public static final boolean DEFAULT_TRACING = false;
  public static final Level DEFAULT_LOGLEVEL = Level.CONFIG;
  public static final Level DEFAULT_TRACELEVEL = Level.FINE;
  public static final Level EXTRA_TRACELEVEL = Level.FINER;

  private String dialect_ = DEFAULT_EXTENSION;
  
  public static final String  SECTION_MANAGER_LIST_PROPERTY_SEPARATOR = File.pathSeparator;
  

  /**
   * The Cache, a mapping from Key to Object. For each (key, object) pair, the object
   * must be an instance of key.getType(). It is the resource computed by each command
   * associated with the key's type.
   */
  private Map<Key<?>, Object> content_ = new HashMap<Key<?>, Object>();

  /**
   * Mapping of dependencies from (LHS) Key to the set of other (RHS) keys that depend on it.
   * That is, it's an upward dependency chain. So, for instance, if
   *
   * A parents Prelude
   * B parents A
   * C parents B
   *
   * We would have a mapping that
   *
   * A -> { B }
   * B -> { C }
   * C -> { }
   *
   * This way, when removing dependencies for A, we know that B and all its dependencies need removing.
   * This way, we calculate the upwards transitive closure of dependencies. So, if A is removed
   * then by calculating the transitive closure of dependencies we would get that { B, C } need removing as well.
   */
  private Map<Key<?>, Set<Key<?>>> dependants_ = new HashMap<Key<?>, Set<Key<?>>>();

  /**
   * The inverse map as above (e.g., downward dependencies). This is almost the transitive parents
   * relationship, but might also include source locator and other keys.
   */
  private Map<Key<?>, Set<Key<?>>> dependencies_ = new HashMap<Key<?>, Set<Key<?>>>();

  /**
   * The default commands. They are those classes capable of computing instances
   * of the resource class that comes from some key.getType().
   */
  private Map<Class<?>,Command> commands_ = new HashMap<Class<?>,Command>();

  /**
   * Properties are used to store global settings
   * for the commands.
   */
  private Properties properties_ = new Properties();

  //TODO: make these part of the managed properties?

  /**
   * Determines whether console handling is on or off messages. Trace format
   * is determined by the <code>SimpleFormatter</code> local class below and
   * it used a <code>ConsoleHandler</code>. Each FINE trace has a call depth
   * number attached to it. It means how deep in the command computation call
   * it occurred. For instance "SM-UPDATE-2" it means that <code>put</code>
   * has been called from within two <code>get</code> contexts.
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
  private ConsoleHandler consoleHandler_ = new ConsoleHandler();

    /**
   * Stack containing its originating key and associated point in the dependencies list where
   * information (e.g., keys) get derived from. That is, the top of the stack is the current
   * in the transaction, and all keys in the dependencies list from its integer number to the
   * length of the list are the (transitive) dependencies to calculate the given key in the pair.
   */
  private final Stack<Pair<Key<?>, Integer>> transactionStack_ = new Stack<Pair<Key<?>, Integer>>();

  private final Stack<Key<?>> postponedTransactionsStack_ = new Stack<Key<?>>();

  /**
   * List of keys in the dependencies involved to calculate a particular key, which *must* belong
   * to the transaction stack
   */
  private final List<Key<?>> dependenciesList_ = new ArrayList<Key<?>>();

  /*@invariant forall (k, i) in transactionStack.listIterator().previous() :
          // from the stack top downwards, the dependencies list point must be within range
          i < dependenciesList_.lentgh &&
          // indexes are order within the stack; but might be the same, when there are no dependencies to be considered
          hasPrevious() -> previous().i <= i
   */

  private final /*Set<Key<?>>*/ Set<String> permanentKeys_ = new HashSet<String>();


  /**
   * 
   */
  public SectionManager()
  {
    this(DEFAULT_EXTENSION);
  }

  /** Creates a new section manager for a given Z extension/dialect.
   *  It calls putCommands(extension) to 
   * @param extension  A Z dialect ("z", "zpatt", "oz", "circus", etc.)
   */
  public SectionManager(String extension)
  {
    this(extension, DEFAULT_TRACING, DEFAULT_LOGLEVEL, DEFAULT_TRACELEVEL);
  }

  public SectionManager(String extension, boolean doTrace, Level logLevel, Level tracingLevel)
  {
    // create a console handler for tracig with simple formatting (see Formatter below).
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

  public String getDialect()
  {
    return dialect_;
  }

  /**
   * <p>Returns a new SectionManager with the same content, commands,
   * and properties.</p>
   *
   * <p>The maps for storing content, commands, and properties are
   * copied, however the content of the maps is <B>not</B> copied.
   * That is, content can be added to the new section manager without
   * affecting the old one, but destructive changes to its content will
   * show up in this section manager as well.
   * </p>
   * @return
   */
  @Override
  public SectionManager clone()
  {
    // don't reset if there are any ongoing transactions
    assertTransactionStackEmpty(null);

    // TODO: perhaps allow clonning half ways through transacytion and then
    //       cancel whatever wasn't finished? The key problem are explicit dependencies

    SectionManager result = new SectionManager(dialect_, isTracing_, logLevel_, tracingLevel_);
    result.permanentKeys_.addAll(permanentKeys_);
    copyMap(content_, result.content_);
    copyMap(commands_, result.commands_);
    copyMap(properties_, result.properties_);
    copyMap(dependants_, result.dependants_);
    copyMap(dependencies_, result.dependencies_);

    // don't copy the stacks or dependencies list

    return result;
  }

  @Override
  public String toString()
  {
    return "SectionManager contains " + mapToString(content_);
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

  @Override
  public boolean isPermanentKey(Key<?> key)
  {
    // cyclic sections management is also permanent (?) TODO: ask andrius...
    //return isPermanentToolkitKey(key) || key.getName().equals("cyclic-parse-manager");
    return permanentKeys_.contains(key.getName());
  }

  /**
   * Deletes entries in the cache that are not called "prelude" and
   * that do not end with "_toolkit".
   */
  @Override
  public void reset()
  {
    // don't reset if there are any ongoing transactions
    assertTransactionStackEmpty(null);

    getLogger().finest("Resetting section manager key-mapped resources.");
    List<Key<?>> keys = new ArrayList<Key<?>>(content_.keySet().size());
    for (Iterator<Key<?>> iter = content_.keySet().iterator(); iter.hasNext();) {
      final Key<?> key = iter.next();
      final String name = key.getName();
      if (!isPermanentKey(key))
      {
        keys.add(key);
      }
    }
    for (Key<?> dKey : keys)
    {
      removeKey(dKey);
    }
    if (isTracing_)
    {
      final String msg = "Remaining resources = " + content_.keySet();
      getLogger().fine(msg);
    }
  }

  private static <E,F> void copyMap(Map<E,F> from, Map<E,F> to)
  {
    to.clear();
    for (Map.Entry<E,F> entry : from.entrySet()) {
      to.put(entry.getKey(), entry.getValue());
    }
  }

  private String collectionsToString(Collection<?> c)
  {
    StringBuilder str = new StringBuilder("[\n\t\t");
    for (Object o : c)
    {
      str.append(o.toString());
      str.append("\n\t\t");
    }
    str.append("]");
    return str.toString(); //c.toString().replaceAll("\\),", "\\)\n\t\t");
  }

  private String mapToString(Map<?, ?> m)
  {
    return m.toString().replaceAll("\\),", "\\)\n\t\t");
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
   * This sets all the properties defined by <code>props</code>
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
      result = Integer.valueOf(value);
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
  public final void putCommands(String extension)
  {
    getLogger().log(Level.FINEST, "Set extension to ''{0}''", extension);
    URL url = getClass().getResource("/" + extension + ".commands");
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
   * @throws NullPointerException if url is <code>null</code>.
   */
  public void putCommands(URL url)
  {
    getLogger().log(Level.FINEST, "Load commands from URL ''{0}''", url);
    final String errorMessage = "Error while loading default commands " +
      "for the section manager: Cannot open " + url.toString();
    try {
      Properties props = new Properties();
      InputStream is = url.openStream();
      if (is != null) {
        props.loadFromXML(is);
        putCommands(props);
        return;
      }
      getLogger().warning(errorMessage);
      throw new RuntimeException(errorMessage);
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
   * checks transaction stack elements
   * @param expected might be null
   * @throws SectionInfoException if empty
   */
  protected void assertTransactionStackNotEmpty(Key<?> expected) throws SectionInfoException
  {
    if (!hasTransaction())
    {
      final String msg = "Transaction stack is empty" +
              "\n\tKey.....: " + String.valueOf(expected);
      throw new SectionInfoException(msg, new IllegalArgumentException());
    }
  }

  /**
   * checks transaction stack elements
   * @param expected
   * @throws SectionInfoException if not empty
   */
  protected void assertTransactionStackEmpty(Key<?> expected) throws SectionInfoException
  {
    if (hasTransaction())
    {
      final String msg = "Transaction stack is not empty" +
              "\n\tKey.....: " + String.valueOf(expected) +
              "\n\tStack...: " + collectionsToString(transactionStack_);
      throw new SectionInfoException(msg, new IllegalArgumentException());
    }
  }

  protected void assertKeyNotCached(Key<?> key) throws SectionInfoException
  {
    if (isCached(key))
    {
      final String message = "Key " + key + " has already been calculated and cached.";
      getLogger().warning(message);
      throw new SectionInfoException(message);
    }
  }

  /**
   * checks if any of the expected transactions is found. if so raises exception
   * @param expected
   * @throws SectionInfoException if any of the expected transaction keys is found in the transaction stack
   */
  protected void assertNoOngoingTransactionFor(Key<?>... expected) throws SectionInfoException
  {
    Key<?> found = foundTransactionFor(expected);
    if (found != null)
    {
      final String msg = "There is an ongoing transaction for given key" +
            "\n\tKey.....: " + found +
            "\n\tStack...: " + collectionsToString(transactionStack_);
      throw new SectionInfoException(msg, new IllegalArgumentException());
    }
  }

  /**
   * checks if the transaction stack top is the one expected
   * @param expected
   * @throws SectionInfoException if top is not equals to expected.
   */
  protected void assertTransactionStackTopIs(Key<?> expected) throws SectionInfoException
  {
    Key<?> found = currentTransactionKey();
    boolean result = found.equals(expected);
    if (!result)
    {
      final String msg = "Transaction stack top is not the one expected" +
            "\n\tKey expected..: " + String.valueOf(expected) +
            "\n\tKey found.....: " + found +
            "\n\tStack.........: " + collectionsToString(transactionStack_);
      throw new SectionInfoException(msg, new IllegalArgumentException());
    }
  }

  protected void assertPostponedStackTopIs(Key<?> expected) throws SectionInfoException
  {
    assert !postponedTransactionsStack_.isEmpty();
    Key<?> found = postponedTransactionsStack_.peek();
    boolean result = found.equals(expected);
    if (!result)
    {
      final String msg = "Transaction stack top is not the one expected" +
            "\n\tKey expected..: " + String.valueOf(expected) +
            "\n\tKey found.....: " + found +
            "\n\tStack.........: " + collectionsToString(postponedTransactionsStack_);
      throw new SectionInfoException(msg, new IllegalArgumentException());
    }
  }

  /**
   * Checks that the dependency list size is within bound with the given index.
   * @param expected
   * @param idx
   * @throws SectionInfoException if top of the stack
   */
  protected void assertTransDepIndexRange(Key<?> expected, Integer idx) throws SectionInfoException
  {
    assertTransactionStackTopIs(expected);
    assert hasTransaction() && currentTransactionKey().equals(expected);
    if (idx > dependenciesList_.size())
    {
      final String msg = "Dependencies index (" + idx + ") out of bounds for transaction." +
              "\n\tKey.....: " + String.valueOf(expected) +
              "\n\tStack...: " + collectionsToString(transactionStack_);
      throw new SectionInfoException(msg, new IndexOutOfBoundsException());
    }
  }

  /**
   * throws an exception saying the expected key is not the one found - there is a mismatch in the transaction start/end calls.
   * this could also happen if there are no transaction at all.
   *
   * @param expected
   * @param found
   * @return
   * @throws SectionInfoException
   */
  protected SectionInfoException transactionMismatch(Key<?> expected, Key<?> found) throws SectionInfoException
  {
    assertTransactionStackNotEmpty(expected);
    final String msg = "Unmatching transaction." +
              "\n\tKey expected..: " + String.valueOf(expected) +
              "\n\tKey found.....: " + String.valueOf(found)+
              "\n\tStack...: " + collectionsToString(transactionStack_);
    return new SectionInfoException(msg);
  }

  protected void assertNoPendingTransactionFor(Key<?> keyToCheck) throws SectionInfoException
  {
    if (postponedTransactionsStack_.contains(keyToCheck))
    {
      final String msg = "Duplicate postponement of transaction: key already postponed." +
              "\n\tKey.....: " + String.valueOf(keyToCheck) +
              "\n\tStack...: " + collectionsToString(transactionStack_) +
              "\n\tPStack..: " + collectionsToString(postponedTransactionsStack_);
      throw new SectionInfoException(msg);
    }
  }

  protected boolean hasTransaction()
  {
    return !transactionStack_.isEmpty();
  }

  /**
   * search through the transaction stack for each of the expected given keys.
   * it returns the first one found or null if none is found.
   * @param expected
   * @return first key found on the transaction stack from the array of keys passed
   */
  protected Key<?> foundTransactionFor(Key<?>... expected)
  {
    Key<?> result = null;
    if (expected != null)
    {
      for(Pair<Key<?>, Integer> p : transactionStack_)
      {
        // TODO: if there is a list "k1, null, k2" will this give a null e or throw a NPE?
        for(Key<?> e : expected)
        {
          if (p.getFirst().equals(e))
          {
            result = e;
            break;
          }
        }
      }
    }
    return result;
  }

  protected Key<?> currentTransactionKey() 
  {
    assertTransactionStackNotEmpty(null);
    return transactionStack_.peek().getFirst();
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
  @SuppressWarnings("unchecked")
  public <T> Set<Key<T>> keysOf(Class<T> clsName)
  {
    Set<Key<T>> result = new HashSet<Key<T>>();
    for (Key<?> k : content_.keySet())
    {
      if (clsName.isAssignableFrom(k.getType()))
      {
        result.add((Key<T>)k);
      }
    }
    return result;
  }

  /**
   * Returns whether the given Key has already been computed
   * and is cached.
   * @param <T>
   */
  @Override
  public <T> boolean isCached(Key<T> key)
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
  @SuppressWarnings("unchecked")
  public <T> Key<T> retrieveKey(T value)
  {
    Key<T> result = null;

    Iterator<Map.Entry<Key<?>, Object>> iter = content_.entrySet().iterator();
    while (iter.hasNext())
    {
      Map.Entry<Key<?>, Object> nextEntry = iter.next();

      // this type-correctness should always be the case
      // i.e., key-associated elements have the type of the key.
      // @czt.todo: how to say this in the declaration of content_?
      T next = (T)nextEntry.getValue();
      if (next.equals(value))
      {
        result = (Key<T>) nextEntry.getKey();

        // TODO: if a key is found for the value, check there isn't an ongoing transaction?
        //       no need, since it will already be for a finished transaction?
        //
        //       don't care, given the key will be the same anyway?
        //assertNoOngoingTransactionFor(result);

        break;
      }
    }
    // result != null => isCached(result)
    // result == null | isCached(result)
    assert result == null || isCached(result) :
      "section manager inconsistency: found a key for given value that is not cached.";
    return result;
  }

  @Override
  public boolean hasTransaction(Key<?> key)
  {
    Key<?> result = foundTransactionFor(key);
    return result != null;
  }


  /**
   * Add a new (Key,Object) pair. It is an error to call put with an existing key.
   * Dependencies are trivial: this is just a degenerate transaction (i.e., start/end)
   * with no extra (e.g., empty) explicit dependencies.
   *
   * @param <T> key type
   * @param key    The key to be added (must not be null).
   * @param value  The value; must be an instance of key.getType().
   * @throws SectionInfoException
   * deprecated
   */
  @Override
  //Deprecated
  public <T> void put(Key<T> key, T value) throws SectionInfoException
  {
    put(key, value, Collections.<Key<?>>emptySet());
  }

  /**
   * Maps the given key to the given value in the section manager. It works by creating
   * a transaction on the key and immediately ending it with the extra dependencies.
   *
   * @param <T> key type
   * @param key    The key to be added (must not be null).
   * @param value  The value; must be an instance of key.getType().
   * @param explicitDependencies dependant keys
   * @throws SectionInfoException
   * deprecated use start/end transaction
   */
  @Override
  //Deprecated
  public <T> void put(Key<T> key, T value, Set<? extends Key<?>> explicitDependencies) throws SectionInfoException
  {
    startTransaction(key);
    endTransaction(key, value, explicitDependencies);
  }

  @Override
  public <T> void ensureTransaction(Key<T> key) throws SectionInfoException
  {
    if (isTracing_)
    {
      final String msg = "SM-ENSURE-TRANSACTION-T"+ (transactionStack_.size()+1)
              +"\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t caller = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }
    if (!hasTransaction(key))
    {
      startTransaction(key);
    }
  }

  @Override
  @SuppressWarnings("unchecked")
  public <T> void startTransaction(Key<T> key) throws SectionInfoException
  {
    if (isTracing_)
    {
      final String msg = "SM-START-TRANSACTION-T"+ (transactionStack_.size()+1)
              +"\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t caller = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }

    // check for key duplication
    assertNoOngoingTransactionFor(key);

    assertKeyNotCached(key);

    // if there is any postponed transactions, check they match with current request
    if (!postponedTransactionsStack_.isEmpty())
    {
      // check postponed stack top is key requested
      assertPostponedStackTopIs(key);
      postponedTransactionsStack_.pop();
    }

    // add the a transaction to the stack, where the dependencies current list state/size
    // determines the pointer where to collect dependencies upon put. Ex: first time it will
    // be empty, hence at index 0. After that, it will one index after the last transactions.
    Pair<Key<T>, Integer> pair = Pair.getPair(key, dependenciesList_.size());
    transactionStack_.push((Pair)pair);
  }

  @Override
  public <T> void endTransaction(Key<T> key, T value) throws SectionInfoException
  {
    endTransaction(key, value, Collections.<Key<?>>emptySet());
  }

  @Override
  public <T> void endTransaction(Key<T> key, T value, Set<? extends Key<?>> explicitDependencies) throws SectionInfoException
  {
    if (key == null || value == null || explicitDependencies == null)
      throw new SectionInfoException("Cannot end transaction with null value or explicit dependencies for key " + key);
    endTransaction0(key, value, explicitDependencies);
  }

  @Override
  public Set<Key<?>> cancelTransaction(Key<?> key) throws SectionInfoException
  {
    if (key == null)
      throw new SectionInfoException("Cannot cancel transaction with null key");
    assertTransactionStackTopIs(key);
    return endTransaction0(key, null, null);
  }

  @Override
  public Set<Key<?>> postponeTransaction(Key<?> currentKeyToCancel, Key<?> nextKeyExpected) throws SectionInfoException
  {
    if (nextKeyExpected == null)
      throw new SectionInfoException("Key expected for the next transaction cannot be null.");

    if (isTracing_)
    {
      final String msg = "SM-POSTPONE-TRANSACTION-T"+ (transactionStack_.size()+1)
              +"\n\t post key = (" + nextKeyExpected.getType().getSimpleName() + ", " + nextKeyExpected.getName() + ")"
              +"\n\t caller   = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }

    // next key cannot have already been cached or put for pending
    assertKeyNotCached(nextKeyExpected);
    assertNoPendingTransactionFor(nextKeyExpected);

    Set<Key<?>> result = cancelTransaction(currentKeyToCancel);
    if (!result.isEmpty()) {
    	// There are keys already marked as transaction's dependencies.
    	// The postpone should only happen as the immediate action in the command,
    	// thus no keys can be marked as dependencies for this transaction.
        final String msg = "Postponing a transaction with dependencies - only " +
        		"fresh transactions (no dependencies) can be postponed." +
                "\n\tKey...........: " + String.valueOf(currentKeyToCancel) +
                "\n\tDependencies..: " + collectionsToString(result) +
                "\n\tStack.........: " + collectionsToString(transactionStack_) +
                "\n\tPStack........: " + collectionsToString(postponedTransactionsStack_);
        throw new SectionInfoException(msg);
    }

    postponedTransactionsStack_.push(nextKeyExpected);
    return result;
  }

  private <T> Set<Key<?>> endTransaction0(Key<T> key, T value, Set<? extends Key<?>> explicitDependencies) throws SectionInfoException
  {
    assert key != null;

    if (isTracing_)
    {
      final String msg = "SM-" + (value == null ? "CANCEL": "END") + "-TRANSACTION-ENTRY-T"+transactionStack_.size()
              +"\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t caller = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }

    // checks there is a trnasaction
    assertTransactionStackNotEmpty(key);

    Set<Key<?>> result;// = Collections.<Key<?>>emptySet();
    Pair<Key<?>, Integer> trans = transactionStack_.peek();

    // check the trasnaction keys match
    if (trans.getFirst().equals(key))
    {
      // check the transaction dependencies index is within range
      assertTransDepIndexRange(key, trans.getSecond());

      // add explicit dependencies to the list
      if (explicitDependencies != null)
      {
        dependenciesList_.addAll(explicitDependencies);
      }

      // the keys involved in the dependency on the key
      List<Key<?>> depOfKey = dependenciesList_.subList(trans.getSecond(), dependenciesList_.size());
      result = new HashSet<Key<?>>(depOfKey);

      // add the mapping and create dependant/dependencies maps
      // non null value = end transaction
      if (value != null)
      {
        // only map the dependencies from the pointer in the transitive dependencies list / set
        addKeyMapping(key, value, result);
      }
      // null value = cancel transaction - return the dependencies to the point.
      else
      {
        // remove the dependencies from list to the point.
        // this does not affect the result returned
        depOfKey.clear();

        // result contains the outermost dependencies that are being cancelled
        // innermost transactions that finished successfully are not cancelled.
      }
      
      // pops the stack to end the transaction
      Pair<Key<?>, Integer> top = transactionStack_.pop();
      assert trans.equals(top);

      // for cancelling transactions wait until the transaction is popped to remove key, if not a permanent one
      if (value == null && !isPermanentKey(key))
      {
        // chase explicit dependencies that might be added for the cancelling key
        removeKey(key);
      }
    }
    else
    {
      // raise the mismatch
      throw transactionMismatch(key, trans.getFirst());
    }
    
    // if this is the last transaction clear the dependencies list
    if (!hasTransaction())
    {
      dependenciesList_.clear();
    }

    if (isTracing_)
    {
      final String msg = "SM-" + (value == null ? "CANCEL": "END") +"-TRANSACTION-EXIT-T"+(transactionStack_.size()+1)
              +"\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t Dep L  = " + collectionsToString(dependenciesList_)
              +"\n\t Stack  = " + collectionsToString(transactionStack_)
              +"\n\t caller = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }
    return result;
  }

  /**
   * Adds a (key, value) mapping to the section manager, where given dependencies (implicit + explicit)
   * are iterated to create the two maps of dependants (downwards) and dependencies (upwards). It also
   * contains a call depth mechanism in order to enable call-stack-based tracing.
   *
   * @param <T> resource key type
   * @param key resource key
   * @param value value to associate with given key
   * @param dependencies ignored for now
   * @param extraCallDepth extra stack depth to consider for caller tracing
   */
  private <T> void addKeyMapping(Key<T> key, T value, Collection<Key<?>> dependencies) throws SectionInfoException
  {
    assert key != null && value != null && dependencies != null;

    assert hasTransaction() && currentTransactionKey().equals(key);

    // check key / value pairs are consistent
    if (!key.getType().isInstance(value))
    {
      final String message = "Section manager inconsistency: "
              + "given value type is not an instance of the associated key"
              + "\n\tKey type....: " + key.getType().getName()
              + "\n\tValue type..: " + value.getClass().getName();
      throw new SectionInfoException(message);
    }

    if (content_.containsKey(key))
    {
      final String message = "Attempt to add duplicate key: " + key;
      getLogger().warning(message);
      // TODO: maybe remove and keep as just a warning?
      throw new SectionInfoException(message);
    }

    content_.put(key, value);
    if (isTracing_ && !isPermanentKey(key))
    {
      final String msg = "SM-UPDATE-"+callCnt_
              +"\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t caller = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }

    HashSet<Key<?>> depSet = new HashSet<Key<?>>(dependencies);

    if (isTracing_)
    {
      // check whether duplicate dependencies arrise and why /when
      final String msg = "SM-GIVEN-DEPENDENCIES_"+callCnt_
              +"\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t dep L  = " + collectionsToString(dependencies)
              +"\n\t dep S  = " + collectionsToString(depSet)
              +"\n\t caller = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }

    // upward dependencies
    //
    // key          = C
    // dependencies = B, A
    // build        = A -> { C }; B -> { C }
    for(Key<?> dk : depSet)
    {
      Set<Key<?>> depOfK = dependants_.get(dk);
      if (depOfK == null)
      {
        depOfK = new HashSet<Key<?>>();
        dependants_.put(dk, depOfK);
      }
      assert depOfK != null;
      depOfK.add(key);
    }

    // @czt.todo is this necessary in the end? say for source locator?
    //
    // downward dependencies
    //
    // key          = C
    // dependencies = B, A
    // build        = C -> { A, B }
    Set<Key<?>> depKeys = dependencies_.get(key);
    if (depKeys == null)
    {
      depKeys = new HashSet<Key<?>>();
      dependencies_.put(key, depKeys);
    }
    depKeys.addAll(dependencies);

    if (isTracing_)
    {
      // check whether duplicate dependencies arrise and why /when
      final String msg = "SM-CALC-DEPENDENCIES_"+callCnt_
              +"\n\t key          = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t dependants   = " + mapToString(dependants_)
              +"\n\t dependencies = " + mapToString(dependencies_)
              +"\n\t caller       = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }
  }

  // TODO: all these methods ought to be transaction aware. that is, they should raise exceptions
  //       in case one wants to remove or query dependencies on ongoing transactions.

  @Override
  public boolean removeKey(Key<?> key)  throws SectionInfoException
  {
    if (isTracing_)
    {
      // check whether duplicate dependencies arrise and why /when
      final String msg = "SM-REMOVE-KEY-T"+transactionStack_.size()
              +"\n\t key          = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t dependants   = " + mapToString(dependants_)
              +"\n\t dependencies = " + mapToString(dependencies_)
              +"\n\t caller       = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }

    // if there are any transactions on key, raise exception
//    assertNoOngoingTransactionFor(key);

    // remove dependants / dependencies
    removeDependants(key);
    removeDependencies(key);

    // remove contents
    Object old = content_.remove(key);
    return old != null;
  }

  private void removeDependants(Key<?> key) throws SectionInfoException
  {
    // if there are any transaction on any dependant, raise exception
    // that can only happen if the user mistakenly start a transaction
    // of something that is already cached.
//    assertNoOngoingTransactionFor(dependants_.keySet().toArray(new Key<?>[0]));

    // clear the dependency list - otherwise recursive removal
    // may loop if there are cyclic dependencies
    Set<Key<?>> depKeys = dependants_.remove(key);
    if (depKeys != null)
    {
      for(Key<?> dkey : depKeys)
      {
        removeKey(dkey);
      }
    }
  }

  private void removeDependencies(Key<?> key) throws SectionInfoException
  {
    // if there are any transaction on any dependencies, raise exception
//    assertNoOngoingTransactionFor(key);

    dependencies_.remove(key);
  }

  @Override
  public Set<Key<?>> getDependants(Key<?> key)  throws SectionInfoException
  {
    // if there are any transaction on given dependants, raise exception
    assertNoOngoingTransactionFor(key);
    // TODO: is this a unnecessary restriction? SEE CHECK???

    Set<Key<?>> result = dependants_.get(key);
    return result == null ? Collections.<Key<?>>emptySet() : Collections.unmodifiableSet(result);
  }

  @Override
  public Set<Key<?>> getDependencies(Key<?> key)  throws SectionInfoException
  {
    // if there are any transaction on any dependencies, raise exception
    assertNoOngoingTransactionFor(key);
    Set<Key<?>> result = dependencies_.get(key);
    return result == null ? Collections.<Key<?>>emptySet() : Collections.unmodifiableSet(result);
  }

  /**
   * <p>
   * Lookup a key in the section manager. It should never return <code>null</code>.
   * That means, it calculates with the command associated with the key type, the
   * resulting value for that key. If it is already present (i.e., {@link #isCached(Key)} is true),
   * then no further calculation is needed. 
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
   *          <dl>SpecSource</dl>
   *              <dd>   
   *              File source for the SpecReader tool, which allows the right
   *              processing of specifications with multiple Z sections per file.
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
   *      See {@link #SourceLocator} for details.
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
   */
  @Override
  @SuppressWarnings("unchecked")
  public <T> T get(Key<T> key) throws CommandException
  {
    if (isTracing_ && !isPermanentKey(key))
    {
      // log the SM query
      final String msg0 = "SM-QUERY -ENTRY-"+callCnt_
              + "\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              + "\n\t caller = " + whoWasCalling(0)
              + "\n";
      getLogger().finer(msg0);
      // enter a request context
      callCnt_++;
    }

    // add the dependency key at this level - implicit dependencies within current transaction, if any
    // (e.g., avoid tracking keys when there are no pending transactions).
    if (hasTransaction())
    {
      dependenciesList_.add(key);
    }

    final Class<T> infoType = key.getType();
    final String name = key.getName();
    boolean cached = true;
    @SuppressWarnings("unchecked")
    T result = (T)content_.get(key);
    if (result == null)
    {
      cached = false;
      Command command = commands_.get(infoType);
      if (command == null)
      {
        throw new UnknownCommandException("No command available to compute " + key);
      }
      // starts a transaction for the given key if not cached
      startTransaction(key);
      // make the actual request
      try
      {
        boolean cres = command.compute(name, this);
      }
      catch (CommandException e)
      {
        // if the command computation throws an exception
        // cancel the transaction that has just been started
        // unless the user has already canceled herself
        // (e.x., LMF or any other situation needing reordering
        //  of the transaction protocol) - we have here a linient
        // cancellation process where the default cancellation can
        // be overriden
        if (hasTransaction(key))
        {
          // if there is a transaction for the key, we cancel it.
          // however, if the key is not on the top of the stack,
          // the user-command/manual-cancellation has made a mistake
          // somewhere and cancelling will throw an exception.
          cancelTransaction(key);
        }
        throw e;
      }
      result = (T)content_.get(new Key<T>(name, infoType)); // why do we need a new key here?
      if (result == null)
      {
        final String message = "Key " + key + " not computed by " + command;
        throw new CommandException(message);
      }
    }
    assert result != null : "Section manager computed null result!";

    if (isTracing_ && !isPermanentKey(key))
    {
      // close the context
      callCnt_--;
      // log SM query results
      final String msg1 = "SM-QUERY -EXIT-"+callCnt_
              + "\n\t result = " + result.getClass().getName()
              + "\n\t dep L  = " + collectionsToString(dependenciesList_)
              + "\n\t cached = " + cached
              + "\n";
      getLogger().finer(msg1);
    }
    return result;
  }

  private int callCnt_ = 0;

  private String whoWasCalling(int extraCallDepth)
  {
    Throwable t = new Throwable();
    t.fillInStackTrace();
    StackTraceElement[] stes = t.getStackTrace();
    if (stes != null && stes.length >= (3+extraCallDepth))
    {
      final String msg = stes[2+extraCallDepth].getClassName() + "." + stes[2+extraCallDepth].getMethodName() + ", " + stes[2+extraCallDepth].getLineNumber();
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

  class SimpleFormatter extends Formatter
  {

    private Date dat = new Date();
    private final static String format = "{0,date} {0,time}";
    private java.text.MessageFormat formatter;
    private Object args[] = new Object[1];
    private boolean fShowTimeStamp = true;
    private boolean fShowRecordedMessage = true;
    private boolean fShowSourceMethod = true;
    private boolean fShowStackTrace = true;
    // Line separator string.  This is the value of the line.separator
    // property at the moment that the SimpleFormatter was created.
    //private String lineSeparator = (String) java.security.AccessController.doPrivileged(
    //        new sun.security.action.GetPropertyAction("line.separator"));
    private String lineSeparator = "\r\n";//System.getProperty("line.separator");
    public SimpleFormatter(boolean showTimeStamp, boolean showRecordedMessage,
      boolean showSourceMethod, boolean showStackTrace)
    {
      fShowTimeStamp = showTimeStamp;
      fShowRecordedMessage = showRecordedMessage;
      fShowSourceMethod = showSourceMethod;
      fShowStackTrace = showStackTrace;
    }

    /**
     * Format the given LogRecord.
     * @param record the log record to be formatted.
     * @return a formatted log record
     */
    @Override
    public synchronized String format(java.util.logging.LogRecord record)
    {
      StringBuilder sb = new StringBuilder();
      if (fShowTimeStamp)
      {
        // Minimize memory allocations here.
        dat.setTime(record.getMillis());
        args[0] = dat;
        StringBuffer text = new StringBuffer();
        if (formatter == null)
        {
          formatter = new java.text.MessageFormat(format);
        }
        formatter.format(args, text, null);
        sb.append(text);
        sb.append(" ");
        sb.append(lineSeparator);
      }
      if (fShowSourceMethod)
      {
        if (record.getSourceClassName() != null)
        {
          sb.append(record.getSourceClassName());
        }
        else
        {
          sb.append(record.getLoggerName());
        }
        if (record.getSourceMethodName() != null)
        {
          sb.append(" ");
          sb.append(record.getSourceMethodName());
        }
        sb.append(lineSeparator);
      }
      if (fShowRecordedMessage)
      {
        String message = formatMessage(record);
        sb.append(record.getLevel().getLocalizedName());
        sb.append(": ");
        sb.append(message);
        sb.append(lineSeparator);
      }
      if (fShowStackTrace)
      {
        if (record.getThrown() != null)
        {
          try
          {
            java.io.StringWriter sw = new java.io.StringWriter();
            java.io.PrintWriter pw = new java.io.PrintWriter(sw);
            record.getThrown().printStackTrace(pw);
            pw.close();
            sb.append(sw.toString());
          }
          catch (Exception ex)
          {
          }
        }
      }
      return sb.toString();
    }
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
}
