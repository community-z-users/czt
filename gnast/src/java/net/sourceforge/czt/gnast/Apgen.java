/**
Copyright 2003 Petra Malik
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

package net.sourceforge.czt.gnast;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import org.apache.velocity.app.Velocity;
import org.apache.velocity.exception.ParseErrorException;
import org.apache.velocity.exception.ResourceNotFoundException;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.Template;
import org.apache.xalan.xsltc.runtime.BasisLibrary;

import net.sourceforge.czt.gnast.pux.PuxProject;
import net.sourceforge.czt.gnast.schema.SchemaProject;

/**
 * <p>An all-purpose text/code generation class
 * that uses velocity.</p>
 *
 * <p>This class provides methods to apply a velocity template
 * by using some kind of context information.  Its main purpose is to
 * hide the confusing exceptions thrown by velocity and to provide
 * some convenient methods to obtain the context from java properties.
 * </p>
 *
 * @author Petra Malik
 */
public class Apgen
{
  // #################### MEMBER VARIABLES ####################

  /**
   * The class name of this class, used for logging purposes.
   */
  public final static String sClassName = "Apgen";

  /**
   * The methods of this class use this logger
   * when providing logging information.
   */
  public final static Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast" + "." + sClassName);

  /**
   * The name of a velocity template file.
   */
  private String mTemplate = null;

  /**
   * The velocity context.
   */
  private VelocityContext mContext = new VelocityContext();

  /**
   * The output writer.
   */
  private Writer mWriter = new OutputStreamWriter(System.out);

  // #################### CONSTRUCTORS ####################

  public Apgen()
  {
    init();
  }

  public Apgen(String templateFile)
  {
    init();
    mTemplate = templateFile;
  }

  public Apgen(String templateFile, Map map)
  {
    init();
    mTemplate = templateFile;
    addToContext(map);
  }

  public Apgen(Map map)
  {
    init();
    addToContext(map);
  }

  // #################### METHODS ####################

  public void init()
  {
    try {
      Velocity.init("velocity.properties");
    } catch(Exception e) {
      sLogger.severe("Cannot initialise velocity.");
    }
  }

  public String getTemplate()
  {
    return mTemplate;
  }

  public void setTemplate(String templateName)
  {
    mTemplate = templateName;
  }

  public Writer getWriter()
  {
    return mWriter;
  }

  public void setWriter(Writer writer)
  {
    mWriter = writer;
  }

  /**
   * Adds the given map to the context, if
   * all the keys in that map are of type String.
   * All occurrences of "." in a key are replaced by "_",
   * since it is not possible to access keys containing dots
   * from a velocity template.
   * The context is left unchanged, if <code>map</code>
   * is <code>null</code>.
   *
   * @throws ClassCastException if the key of the mapping is not
   *                            a string.
   * @czt.todo Insert strings containing a dot as a map into a
   *           velocity context?
   */
  public void addToContext(Map map)
  {
    final String methodName = "addToContext";
    sLogger.entering(sClassName, methodName, map);
    if (map == null || map.entrySet() == null) return;
    for (Iterator iter = map.entrySet().iterator(); iter.hasNext();) {
      Map.Entry entry = (Map.Entry) iter.next();
      String key = (String) entry.getKey();
      key = key.replace('.', '_');
      Object value = entry.getValue();
      addToContext(key, value);
    }
    sLogger.exiting(sClassName, methodName);
  }

  /**
   * @throws ClassCastException if one of the keys of the mapping is not
   *                            a string.
   * @throws NullPointerException if the map or the name is <code>null</code>.
   */
  public static Map parseMap(Map map, String name)
  {
    final String methodName = "parseMap";
    sLogger.entering(sClassName, methodName);
    Map erg = new HashMap();
    for (Iterator iter = map.entrySet().iterator(); iter.hasNext();) {
      Map.Entry entry = (Map.Entry) iter.next();
      String s = (String) entry.getKey();
      if (s.startsWith(name + ".")) {
	String key = s.substring(name.length() + 1, s.length());
	Object value = entry.getValue();
	erg.put(key, value);
      }
    }
    sLogger.exiting(sClassName, methodName, erg);
    return erg;
  }

  /**
   * Adds a name/value pair to the context.
   *
   * @param name The name.
   * @param value The corresponding value.
   */
  public void addToContext(String name, Object value)
  {
    final String methodName = "addToContext";
    sLogger.entering(sClassName, methodName, name);
    mContext.put(name, value);
    sLogger.exiting(sClassName, methodName);
  }

  /**
   * Removes the mapping for this key from this map if it is present.
   *
   * @param key key whose mapping is to be removed from the map.
   */
  public Object removeFromContext(String key)
  {
    return mContext.remove(key);
  }

  /**
   * A low-level call to velocity.
   * Throws all the exceptions that velocity throws.
   *
   * @throws ParseErrorException if the template cannot be parsed.
   * @throws ResourceNotFoundException if one of the resources cannot
   *                                   be found.
   * @throws IOException if the writer cannot be flushed.
   * @throws Exception for any other error.
   * @see #generate
   */
  public void generateLowLevel()
    throws ParseErrorException, ResourceNotFoundException, Exception
  {
    final String methodName = "generateLowLevel";
    sLogger.entering(sClassName, methodName);
    sLogger.fine("Use template file " + mTemplate + ".");
    sLogger.fine("Use context " + mContext + ".");
    sLogger.fine("Use writer " + mWriter + ".");
    Template template = Velocity.getTemplate(mTemplate);
    template.merge(mContext, mWriter);
    mWriter.flush();

    sLogger.exiting(sClassName, methodName);
  }

  /**
   * Tries to apply the template using the context and writer
   * and returns whether this attempt was successful or not.
   * Logging to the given level is provided in case of an error
   * (for instance, if the template file could not be found).
   * A parse error in the template file is treated as a serious
   * programming error and a <code>GnastException</code> is thrown.
   *
   * @return <code>true</code> if the generation was successful;
   *         <code>false</code> otherwise.
   * @throws NullPointerException if the template, the context
   *                              or the writer is <code>null</code>.
   * @throws GnastException if there was a parse error in the
   *                        template file.
   */
  public boolean generate(Level level)
  {
    final String methodName = "generate";
    boolean success = false;

    sLogger.entering(sClassName, methodName);
    sLogger.fine("Use template file " + mTemplate + ".");
    sLogger.fine("Use context " + mContext + ".");
    sLogger.fine("Use writer " + mWriter + ".");
    if (mTemplate == null ||
	mContext == null ||
	mWriter == null) {
      throw new NullPointerException();
    }
    try {
      generateLowLevel();
      success = true;
    } catch(ParseErrorException e) {
      throw new GnastException("Parse error in " + mTemplate + ".", e);
    } catch(ResourceNotFoundException e) {
      sLogger.log(level, e.getMessage());
      //      e.printStackTrace();
      success = false;
    } catch(IOException e) {
      sLogger.log(level, e.getMessage());
    } catch(Exception e) {
      sLogger.log(level, "Cannot apply template file " + mTemplate + ".");
      //      e.printStackTrace();
      success = false;
    }
    sLogger.exiting(sClassName, methodName, new Boolean(success));
    return success;
  }

  /**
   * The main method.
   */
  public static void main (String[] args)
    throws Exception
  {
    String usage = sClassName + " class options:\n";
    usage += "  -p, --prop <file> The property file.\n";
    usage += "  -t, --template <file> The template file.\n";
    usage += " [-c, --class <name> The class name.]\n";

    int i = 0;
    String propertyFile = null;
    String templateFile = null;
    String name = null;

    while (i < args.length && args[i].startsWith("-")) {
      String arg = args[i++];
      if (arg.equals("-p") ||
	       arg.equals("--prop") ||
	       arg.equals("-prop"))
      {
	if (i < args.length) {
	  propertyFile = args[i++];
	} else {
	  System.err.println(arg + " requires a file name.");
	  System.err.println(usage);
	  return;
	}
      }
      else if (arg.equals("-t") ||
	       arg.equals("--template") ||
	       arg.equals("-template"))
      {
	if (i < args.length) {
	  templateFile = args[i++];
	} else {
	  System.err.println(arg + " requires a file name.");
	  System.err.println(usage);
	  return;
	}
      }
      else if (arg.equals("-c") ||
	       arg.equals("--class") ||
	       arg.equals("-class"))
      {
	if (i < args.length) {
	  name = args[i++];
	} else {
	  System.err.println(arg + " requires a string.");
	  System.err.println(usage);
	  return;
	}
      }
    }
    if (i < args.length ||
	propertyFile == null ||
	templateFile == null) {
      System.err.println(usage);
      return;
    }

    Properties props = new Properties();
    try {
      props.load(new FileInputStream(propertyFile));
    } catch(Exception e) {
      System.err.println(e.getMessage());
    }

    Logger rootLogger = Logger.getLogger("");
    rootLogger.setLevel(Level.ALL);
    Handler handler = null;
    Handler[] h = rootLogger.getHandlers();
    for (i=0; i<h.length; i++) {
      if (h[i] instanceof ConsoleHandler) {
	handler = h[i];
      }
    }
    if (handler == null) {
      handler = new ConsoleHandler();
      rootLogger.addHandler(handler);
    }
    handler.setLevel(Level.INFO);
    //    handler.setLevel(Level.FINER);

    Apgen gen;
    if (name == null) {
      gen = new Apgen(templateFile, props);
    } else {
      gen = new Apgen(templateFile);
      gen.addToContext("class", parseMap(props, name));
    }
    gen.generate(Level.SEVERE);
  }
}
