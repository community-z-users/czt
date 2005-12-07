/*
  Copyright (C) 2004, 2005 Petra Malik
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

import java.io.*;
import java.net.URL;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.logging.Logger;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;

/**
 * This class is a repository for information about Z specs/sections.
 * It stores all the objects used during parsing and transforming,
 * and provides several services like computing the operator table
 * or the markup function for a given section.  Note that the keys
 * to access an object within the section manager are a (Name,Class)
 * pair, which means that several different kinds of objects can be
 * associated with the same name.
 * <p>
 * One of the main goals of this class is to cache commonly used
 * objects (such as the parsed forms of toolkit sections) so that they
 * do not have to be repeatedly parsed.  This can give major performance
 * improvements!
 * </p>
 * <p>  
 * However, a fundamental problem is that things can become
 * inconsistent if you add a section XYZ, then add other sections that
 * use it, then reload a new version of XYZ (the other sections will
 * not notice this, so will still be using the old version of XYZ).
 * </p>
 * <p>
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
 *   <li> <code>oldSectMan.reset()</code> -- currently this clears the
 *        whole cache, but it SHOULD leave the toolkit entries there.</li>
 *   <li> <code>oldSectMan.clone()</code> -- depending upon WHEN you do 
 *        this clone, you can decide just how much you want to leave in
 *        the cache.</li>
 * </ol> 
 * To avoid reparsing toolkits repeatedly (which makes things slow!),
 * you should avoid creating new section managers and use the reset or
 * clone methods instead.
 * </p>
 *
 * @author Petra Malik
 * @author Mark Utting
 */
public class SectionManager
  implements Cloneable, SectionInfo
{
  /**
   * The Cache, a mapping from Key to Object.
   * For each (key, object) pair, the object must be an instance of
   * key.getType().
   */
  private Map<Key,Object> content_ = new HashMap();

  /**
   * The default commands.
   */
  private Map<Class,Command> commands_ = new HashMap();

  /**
   * Properties are used to store persistant global settings
   * for the commands.
   */
  private Properties properties_ = new Properties();

  public SectionManager()
  {
    setupDefaultCommands();
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
   */
  public Object clone()
  {
    SectionManager result = new SectionManager();
    copyMap(content_, result.content_);
    copyMap(commands_, result.commands_);
    copyMap(properties_, result.properties_);
    return result;
  }

  private void copyMap(Map from, Map to)
  {
    to.clear();
    for (Iterator<Map.Entry> i = from.entrySet().iterator(); i.hasNext(); ) {
      Map.Entry entry = i.next();
      to.put(entry.getKey(), entry.getValue());
    }
  }

  /**
   * <p>Returns a property.</p>
   *
   * <p>Properties are used to store persistant global settings
   * for the commands.</p>
   */
  public String getProperty(String key)
  {
    return properties_.getProperty(key);
  }

  /**
   * <p>Returns a property.</p>
   *
   * <p>Properties are used to store persistant global settings
   * for the commands.</p>
   */
  public Properties getProperties()
  {
    return properties_;
  }

  /**
   * <p>Sets a property to the given value.</p>
   *
   * <p>Properties are used to store persistant global settings
   * for the commands.</p>
   */
  public Object setProperty(String key, String value)
  {
    return properties_.setProperty(key, value);
  }

  /**
   * Adds the default commands to the command map.
   */
  public void setupDefaultCommands()
  {
    addCommand("net.sourceforge.czt.session.Source",
               "net.sourceforge.czt.session.SourceLocator");
    addCommand("net.sourceforge.czt.z.ast.Spec",
               "net.sourceforge.czt.parser.z.ParseUtils");
    addCommand("net.sourceforge.czt.z.ast.ZSect",
               "net.sourceforge.czt.parser.z.ParseUtils");
    addCommand("net.sourceforge.czt.parser.util.LatexMarkupFunction",
               "net.sourceforge.czt.parser.z.ParseUtils");
    addCommand("net.sourceforge.czt.parser.util.OpTable",
               "net.sourceforge.czt.parser.util.OpTableCommand");
    addCommand("net.sourceforge.czt.parser.util.DefinitionTable",
               "net.sourceforge.czt.parser.util.DefinitionTableService");
    addCommand("net.sourceforge.czt.parser.util.JokerTable",
               "net.sourceforge.czt.parser.util.JokerTableCommand");
  }

  private boolean addCommand(String type, String commandClassName)
  {
    try {
      Class typeClass = toClass(type);
      Class commandClass = toClass(commandClassName);
      if (typeClass != null && commandClass != null) {
        Object command = commandClass.newInstance();
        if (command instanceof Command) {
          commands_.put(typeClass, (Command) command);
          return true;
        }
        final String message = "Cannot instanciate command " +
          commandClassName + "; given class is not a command";
        CztLogger.getLogger(getClass()).warning(message);      
      }
    }
    catch (ExceptionInInitializerError e) {
      final String message = "Cannot instanciate command " + commandClassName +
        "; exception in initialzier";
      CztLogger.getLogger(getClass()).warning(message);
    }
    catch (IllegalAccessException e) {
      final String message = "Cannot instanciate command " + commandClassName +
        "; illegal access exception";
      CztLogger.getLogger(getClass()).warning(message);
    }
    catch (InstantiationException e) {
      final String message = "Cannot instanciate command " + commandClassName +
        "; instantiation exception";
      CztLogger.getLogger(getClass()).warning(message);
    }
    catch (SecurityException e) {
      final String message = "Cannot instanciate command " + commandClassName +
        "; security exception";
      CztLogger.getLogger(getClass()).warning(message);
    }
    return false;
  }

  /**
   * Returns Class.forName(className) but does not throw exceptions.
   */
  private Class toClass(String name)
  {
    try {
      return Class.forName(name);
    }
    catch (ExceptionInInitializerError e) {
      final String message = "Cannot get class " + name +
        "; exception in initialzier";
      CztLogger.getLogger(getClass()).warning(message);
    }
    catch (LinkageError e) {
      final String message = "Cannot get class " + name +
        "; linkage error";
      CztLogger.getLogger(getClass()).warning(message);
    }
    catch (ClassNotFoundException e) {
      final String message = "Cannot get class " + name +
        "; class cannot be found";
      CztLogger.getLogger(getClass()).warning(message);
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
  public void putCommand(Class infoType, Command command)
  {
    commands_.put(infoType, command);
  }

  /**
   * Returns the command for calculating the given type of information.
   */
  public Command getCommand(Class infoType)
  {
    return commands_.get(infoType);
  }

  /**
   * Returns whether the given Key has already been computed
   * and is cached.
   */
  public boolean isCached(Key key)
  {
    return content_.get(key) != null;
  }

  /**
   * Lookup a key in the section manager.
   * It should never return <code>null</code>.
   *
   * @param key   The key to be looked up.
   * @return      An instance of key.getType().
   * @throws      CommmandException if the lookup was unseccessful.
   */
  public Object get(Key key)
    throws CommandException
  {
    CztLogger.getLogger(getClass()).finer("Entering method get " + key);
    final Class infoType = key.getType();
    final String name = key.getName();
    Object result = content_.get(key);
    if (result == null) {
      Command command = (Command) commands_.get(infoType);
      if (command == null) {
        throw new CommandException("No command available to compute " + key);
      }
      CztLogger.getLogger(getClass()).finer("Try command ...");
      command.compute(name, this);
      result = content_.get(new Key(name, infoType));
      if (result == null) {
        final String message = "Key " + key + " not computed by " + command;
        throw new CommandException(message);
      }
    }
    final String message = "Leaving method get and returning " + result;
    CztLogger.getLogger(getClass()).finer(message);
    return result;
  }

  /**
   * Add a new (Key,Object) pair.
   * It is an error to call add with an existing key.
   *
   * @param key    The key to be added (must not be null).
   * @param value  The value; must be an instance of key.getType().
   */
  public void put(Key key, Object value)
  {
    assert key != null;
    assert value != null;
    if ( ! key.getType().isInstance(value)) {
      String message =
        "SectionManager ERROR: " + value +
        " is not an instance of " + key.getType();
      CztLogger.getLogger(getClass()).warning(message);
    }
    assert key.getType().isInstance(value);
    if (content_.containsKey(key)) {
      String message = "Attempt to add duplicate key: " + key;
      CztLogger.getLogger(getClass()).warning(message);
    }
    content_.put(key, value);
    CztLogger.getLogger(getClass()).finer("put " + key);
  }

  /**
   * Similar to put(key,value).
   * At the moment, the dependencies are ignored.
   */
  public void put(Key key, Object value, Set/*<Key>*/ dependencies)
  {
    put(key, value);
  }

  /**
   * Deletes all entries in the cache.
   *
   * @czt.todo Do not delete toolkit entries.
   */
  public void reset()
  {
    CztLogger.getLogger(getClass()).finer("reset");
    content_.clear();
  }

  public String toString()
  {
    return "SectionManager contains " + content_.toString();
  }

  /**
   * A command to compute the latex markup function (class LatexMarkupFunction)
   * for a Z section.
   */
  class LatexMarkupFunctionCommand
    implements Command
  {
    public boolean compute(String name,
                           SectionManager manager)
      throws CommandException
    {
      Key key = new Key(name, LatexMarkupFunction.class);
      if (! manager.isCached(key)) {
        ZSect zsect = (ZSect) manager.get(new Key(name, ZSect.class));
        if (! manager.isCached(key) && zsect != null) {
          manager.put(key, new LatexMarkupFunction(name));
        }
      }
      return true;
    }
  }
}
