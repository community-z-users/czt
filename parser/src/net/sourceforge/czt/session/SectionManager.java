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
 * It provides several services like computing
 * the markup function for a given section name.
 *
 * @author Petra Malik
 * @author Mark Utting
 */
public class SectionManager
  implements SectionInfo
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
  private Properties properties_;

  public SectionManager()
  {
    setupDefaultCommands();
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
  private void setupDefaultCommands()
  {
    commands_.put(Source.class, new SourceLocator());
    commands_.put(Spec.class, ParseUtils.getCommand());
    commands_.put(ZSect.class, ParseUtils.getCommand());
    commands_.put(OpTable.class, new OpTableCommand());
    commands_.put(DefinitionTable.class, new DefinitionTableService());
    commands_.put(LatexMarkupFunction.class, ParseUtils.getCommand());
    commands_.put(JokerTable.class, new JokerTableCommand());
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
   * Lookup a key in the section manager.
   *
   * @param key   The key to be looked up.
   * @return      An instance of key.getType(), or null.
   */
  public Object get(Key key)
  {
    CztLogger.getLogger(getClass()).finer("Entering method get " + key);
    final Class infoType = key.getType();
    final String name = key.getName();
    Object result = content_.get(key);
    if (result == null && commands_.get(infoType) != null) {
      Command command = (Command) commands_.get(infoType);
      try {
        CztLogger.getLogger(getClass()).finer("Try command ...");
        command.compute(name, this);
        result = content_.get(new Key(name, infoType));
      }
      catch (Exception e) {
        e.printStackTrace();
        final String message = "Caught exception " + e.getClass().getName() +
          " while computing " + key +
          ": " + e.getMessage();
        CztLogger.getLogger(getClass()).warning(message);
        result = null;
      }
    }
    final String message = "Leaving method get and returning " + result;
    CztLogger.getLogger(getClass()).finer(message);
    return result;
  }

  /**
   * Lookup information in the section manager.
   *
   * @param name     The name to be looked up.
   * @param infoType The type of information (content) to be looked up.
   * @return         An instance of key.getType(), or null.
   * @deprecated     Replaced by {@link #get(Key)}
   */
  public Object getInfo(String name, Class infoType)
  {
    Key key = new Key(name, infoType);
    return get(key);
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

  /**
   * @deprecated     Replaced by {@link #put(Key, Object)}
   */
  public Term addLatexSpec(String latexSpec)
    throws ParseException
  {
    Spec spec = (Spec) ParseUtils.parseLatexString(latexSpec, this);
    for (Iterator iter = spec.getSect().iterator(); iter.hasNext(); ) {
      Object o = iter.next();
      if (o instanceof ZSect) {
        ZSect zSect = (ZSect) o;
        put(new Key(zSect.getName(), ZSect.class), zSect);
      }
    }
    return spec;
  }

  /**
   * @deprecated     Replaced by {@link #get(Key)}
   */
  public Term getAst(URL url)
    throws ParseException, IOException
  {
    Key key = new Key(url.toString(), Spec.class);
    Spec spec = (Spec) get(key);
    assert spec == null; // user should have called reset() before re-parsing.
    spec = (Spec) ParseUtils.parse(url, this);
    put(key, spec);
    return spec;
  }

  public String toString()
  {
    return "SectionManager contains " + content_.toString();
  }

  /**
   * A command to compute the URL for a Z section.
   */
  class SourceLocator
    implements Command
  {
    public boolean compute(String name,
                           SectionManager manager)
      throws Exception
    {
      URL url = getClass().getResource("/lib/" + name + ".tex");
      if (url != null) {
        manager.put(new Key(name, Source.class), new UrlSource(url));
	return true;
      }
      File file = new File(name);
      if (file.exists()) {
	manager.put(new Key(name, Source.class), new FileSource(file));
	return true;
      }
      return false;
    }
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
      throws Exception
    {
      Source source = (Source) manager.get(new Key(name, Source.class));
      LatexToUnicode l2u = new LatexToUnicode(source,
                                              manager,
                                              manager.getProperties());
      while (l2u.next_token().sym != LatexSym.EOF) {
        // do nothing
      }
      return true;
    }
  }

  /**
   * A command to compute the operator table (class OpTable) of a Z section.
   */
  class OpTableCommand
    implements Command
  {
    public boolean compute(String name,
                           SectionManager manager)
      throws Exception
    {
      Source source = (Source) manager.get(new Key(name, Source.class));
      if (source != null) {
        ParseUtils.parse(source, manager);
        Key key = new Key(name, OpTable.class);
        Object result = (OpTable) manager.get(key);
        if (result == null) {
          OpTableVisitor visitor = new OpTableVisitor(manager);
          ZSect zSect = (ZSect) manager.get(new Key(name, ZSect.class));
          if (zSect != null) {
            result = (OpTable) visitor.run(zSect);
            if (result != null) {
              manager.put(key, result);
            }
          }
        }
      }
      return true;
    }
  }
}
