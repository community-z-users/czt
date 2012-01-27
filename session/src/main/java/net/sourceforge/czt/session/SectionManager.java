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

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
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
import java.util.logging.ConsoleHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * This class is a repository for information about (Z) specs/sections.
 * It stores all the objects used during CZT processing, such as parsing
 * typechecking and so on. It provides several services, depending on the
 * kind of key requested. For instance, it can compute the operator table
 * or the markup function for a given section, or typecheck or domain check
 * a given Term/Spec/ZSect. The keys to access an object within the section
 * manager are a (Name,Class) pair, which means that several different kinds
 * of objects can be associated with the same name.
 * <p>
 * One of the main goals of this class is to cache commonly used
 * objects, such as the parsed forms of toolkit sections, so that they
 * do not have to be repeatedly processed.  This can give great performance
 * improvements.
 * </p>
 * <p>
 * However, a fundamental problem is that things can become
 * inconsistent if you add a section XYZ, then add other sections that
 * uses it, then reload a new version of XYZ (the other sections will
 * not notice this, so will still be using the old version of XYZ).
 * We have no good solution for this at the moment (we have
 * investigated recording dependency information, but found it
 * incredibly hard to get right!).  So our current solution is to
 * leave this consistency issue to the clients!  That is, clients
 * should clone or reset the section manager to avoid adding
 * the same object twice.  If you do try to add the same key twice,
 * the section manager will simply give a warning,
 * "Attempt to add duplicate key:...".  In the future, this will become
 * a fatal error.
 * We are still experimenting with the best approach here.
 * </p>
 * <p>
 * There are currently three ways of getting/reusing a section
 * manager object.
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
 * clone methods instead.
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
 * mapped to the underlyign <code>Spec</code> object resulting from the computation of the command.
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

  private ConsoleHandler consoleHandler_ = new ConsoleHandler();

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

    isTracing_ = false;
    // initialise the logger's handlers + isTracing_ flag via setTracing();
    setTracingLevel(tracingLevel);
    setTracing(doTrace);

    // set the section manager logging level at start
    getLogger().setLevel(logLevel);
    getLogger().log(Level.FINEST, "Creating a new {0} section manager", extension);
    putCommands(extension);
    dialect_ = extension;
  }

  public final Logger getLogger()
  {
    return Logger.getLogger(getClass().getName());
  }

  public String getDialect()
  {
    return dialect_;
  }

  public Level getTracingLevel()
  {
    return tracingLevel_;
  }

  public boolean isTracing()
  {
    return isTracing_;
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
   * @return
   */
  @Override
  public SectionManager clone()
  {
    SectionManager result = new SectionManager(dialect_, isTracing_, logLevel_, tracingLevel_);
    copyMap(content_, result.content_);
    copyMap(commands_, result.commands_);
    copyMap(properties_, result.properties_);
    copyMap(dependants_, result.dependants_);
    copyMap(dependencies_, result.dependencies_);
    return result;
  }

  private static <E,F> void copyMap(Map<E,F> from, Map<E,F> to)
  {
    to.clear();
    for (Map.Entry<E,F> entry : from.entrySet()) {
      to.put(entry.getKey(), entry.getValue());
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
  public boolean removeKey(Key<?> key)
  {
    removeDependants(key);
    removeDependencies(key);
    Object old = content_.remove(key);
    return old != null;
  }

  @Override
  public Set<Key<?>> getDependants(Key<?> key)
  {
    return Collections.unmodifiableSet(dependants_.get(key));
  }

  private void removeDependants(Key<?> key)
  {
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

  private void removeDependencies(Key<?> key)
  {
    dependencies_.remove(key);
  }

  @Override
  public Set<Key<?>> getDependencies(Key<?> key)
  {
    return Collections.unmodifiableSet(dependencies_.get(key));
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
  public <T> T get(Key<T> key)
    throws CommandException
  {
    if (isTracing_)
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

    final Class<?> infoType = key.getType();
    final String name = key.getName();
    boolean cached = true;
    @SuppressWarnings("unchecked")
    T result = (T)content_.get(key);
    if (result == null) {
      cached = false;
      Command command = commands_.get(infoType);
      if (command == null) {
        throw new UnknownCommandException("No command available to compute " + key);
      }
      // make the actual request
      boolean cres = command.compute(name, this);
      result = (T) content_.get(new Key(name, infoType)); // why do we need a new key here?
      if (result == null) {
        final String message = "Key " + key + " not computed by " + command;
        throw new CommandException(message);
      }
    }
    assert result != null : "Section manager computed null result!";

    if (isTracing_)
    {
      // close the context
      callCnt_--;
      // log SM query results
      final String msg1 = "SM-QUERY -EXIT-"+callCnt_
              + "\n\t result = " + result.getClass().getName()
              + "\n\t cached = " + cached
              + "\n";
      getLogger().finer(msg1);
    }
    return result;
  }
  
  /**
   * Add a new (Key,Object) pair.
   * It is an error to call add with an existing key.
   *
   * @param <T> key type
   * @param key    The key to be added (must not be null).
   * @param value  The value; must be an instance of key.getType().
   */
  public <T> void put(Key<T> key, T value)
  {
    put0(key, value, null);
  }

  /**
   * Similar to put(key,value).
   * At the moment, the dependencies are ignored.
   * @param <T> key type
   * @param key    The key to be added (must not be null).
   * @param value  The value; must be an instance of key.getType().
   * @param dependencies dependant keys
   */
  @Override
  public <T> void put(Key<T> key, T value, Set<Key<?>> dependencies)
  {
    put0(key, value, dependencies);
  }

  /**
   * Original version, but with all the parameters plus an extra call depth to
   * consider when using tracing. That is, sometimes, it can be could be called
   * with or without dependencies, and in order to give the right caller's path,
   * this use of put0 is necessary.
   * @param <T> resource key type
   * @param key resource key
   * @param value value to associate with given key
   * @param dependencies ignored for now
   * @param extraCallDepth extra stack depth to consider for caller tracing
   */
  private <T> void put0(Key<T> key, T value, Set<Key<?>> dependencies)
  {
    assert key != null;
    assert value != null;
    if ( ! key.getType().isInstance(value)) {
      String message =
        "SectionManager ERROR: " + value +
        " is not an instance of " + key.getType();
      getLogger().warning(message);
    }
    assert key.getType().isInstance(value);
    if (content_.containsKey(key)) {
      String message = "Attempt to add duplicate key: " + key;
      getLogger().warning(message);
    }
    content_.put(key, value);
    if (isTracing_)
    {
      final String msg = "SM-UPDATE-"+callCnt_
              +"\n\t key    = (" + key.getType().getSimpleName() + ", " + key.getName() + ")"
              +"\n\t caller = " + whoWasCalling(1)
              + "\n";
      getLogger().fine(msg);
    }
    if (dependencies != null)
    {
      // upward dependencies
      //
      // key          = C
      // dependencies = B, A
      // build        = A -> { C }; B -> { C }
      for(Key<?> dk : dependencies)
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
    }
  }

  /**
   * Deletes entries in the cache that are not called "prelude" and
   * that do not end with "_toolkit".
   */
  public void reset()
  {
    getLogger().finest("Resetting section manager key-mapped resources.");
    List<Key<?>> keys = new ArrayList<Key<?>>(content_.keySet().size());
    for (Iterator<Key<?>> iter = content_.keySet().iterator(); iter.hasNext();) {
      final Key<?> key = iter.next();
      final String name = key.getName();
      if (!"prelude".equals(name) &&
          ! name.endsWith("_toolkit")) {
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

  @Override
  public String toString()
  {
    return "SectionManager contains " + content_.toString();
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

  private int callCnt_ = 0;

  private String whoWasCalling(int extraCallDepth)
  {
    Throwable t = new Throwable();
    t.fillInStackTrace();
    StackTraceElement[] stes = t.getStackTrace();
    if (stes != null && stes.length >= (3+extraCallDepth))
    {
      final String msg = stes[2+extraCallDepth].getClassName() + "." + stes[2+extraCallDepth].getMethodName();
      return msg;
    }
    return "????";
  }

  public final Level setTracingLevel(Level level)
  {
    Level result = tracingLevel_;
    tracingLevel_ = level;
    return result;
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
  public final boolean setTracing(boolean on)
  {
    return setTracing(on, consoleHandler_);
  }

  public boolean setTracing(boolean on, Handler handler)
  {
    Logger log = getLogger();
    boolean result = isTracing_;
    isTracing_ = on;
    if (isTracing_)
    {
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
