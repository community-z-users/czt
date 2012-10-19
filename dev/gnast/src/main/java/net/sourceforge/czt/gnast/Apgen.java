/*
  Copyright 2003, 2005, 2006 Petra Malik
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

import org.apache.velocity.exception.ParseErrorException;
import org.apache.velocity.exception.ResourceNotFoundException;
import org.apache.velocity.runtime.RuntimeInstance;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.Template;

/**
 * <p>An All-Purpose text/code GENerator
 * that uses velocity.</p>
 *
 * <p>This class provides methods for applying a velocity template
 * by using some kind of context information.  Its main purpose is to
 * to provide a convenient way to use velocity (for instance,
 * by hiding the confusing exceptions), and to provide
 * some way to obtain the context used by velocity from maps.</p>
 *
 * @author Petra Malik
 */
public class Apgen
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  /**
   * The class name of this class; used for logging purposes.
   */
  public static final String CLASS_NAME = "Apgen";

  /**
   * The logger used when logging information is provided.
   */
  public static final Logger LOGGER =
    Logger.getLogger("net.sourceforge.czt.gnast" + "." + CLASS_NAME);

  /**
   * The velocity runtime environment.
   */
  private RuntimeInstance velocity_ = new RuntimeInstance();

  /**
   * The name of the velocity template file.
   * This file is used when a text/code generation attempt is taken.
   *
   * @see #getTemplate
   * @see #setTemplate
   */
  private String template_ = null;

  /**
   * <p>The velocity context.  The things in here can be accessed
   * within the velocity template file.</p>
   *
   * <p>It should never become <code>null</code>.</p>
   *
   * @see #addToContext(java.util.Map)
   * @see #addToContext(java.lang.String, java.lang.Object)
   * @see #removeFromContext
   */
  private VelocityContext context_ = new VelocityContext();

  /**
   * <p>The output writer where the output is written to.
   * Default is an OutputStreamWriter to system.out.</p>
   *
   * <p>It should never become <code>null</code>.</p>
   *
   * @see #getWriter
   * @see #setWriter
   */
  private Writer writer_ = new OutputStreamWriter(System.out);

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * Creates a new all-purpose text/code generator.
   */
  public Apgen()
  {
    init();
  }

  /**
   * Creates a new all-purpose text/code generator
   * that uses the given velocity template file.
   *
   * @param templateFile the velocity template file to be used.
   */
  public Apgen(String templateFile)
  {
    init();
    template_ = templateFile;
  }

  public Apgen(String templateFile, Map<String, ?> map)
  {
    init();
    template_ = templateFile;
    addToContext(map);
  }

  public Apgen(Map<String, ?> map)
  {
    init();
    addToContext(map);
  }

  public Apgen(Map<String, ?> map, Properties initProps)
  {
    init(initProps);
    addToContext(map);
  }

  // ############################################################
  // ################### (NON-STATIC) METHODS ###################
  // ############################################################

  // ************************** INIT ****************************

  /**
   * Initialises velocity.
   * If this fails, logging information is provided.
   *
   * @czt.todo Throw an exception in case of an error?
   *           There is no useful way to continue after such
   *           an error.
   */
  private void init()
  {
    try {
      velocity_.init("velocity.properties");
    }
    catch (Exception e) {
      LOGGER.severe("Cannot initialise velocity.");
    }
  }

  private void init(Properties initProps)
  {
    try {
      velocity_.init(initProps);
    }
    catch (Exception e) {
      LOGGER.severe("Cannot initialise velocity.");
    }
  }

  // ******************** GETTER AND SETTER *********************

  /**
   * Returns the velocity template file name.
   * The default is <code>null</code>.
   *
   * @return the name of the velocity template file.
   */
  public String getTemplate()
  {
    return template_;
  }

  /**
   * Sets the velocity template file name.
   *
   * @param templateName the new velocity template file.
   */
  public void setTemplate(String templateName)
  {
    template_ = templateName;
  }

  /**
   * Returns the writer used for writing the result.
   * The default is an OutputStreamWriter to System.out.
   *
   * @return the writer used for writing the result
   *         (should never be <code>null</code>).
   */
  public Writer getWriter()
  {
    return writer_;
  }

  /**
   * Sets the writer used for writing the result.
   *
   * @param writer the new writer used for writing the result.
   * @throws NullPointerException if <code>writer</code> is
   *                              <code>null</code>.
   */
  public void setWriter(Writer writer)
  {
    if (writer == null) throw new NullPointerException();
    writer_ = writer;
  }

  // ********************* CONTEXT HANDLING *********************

  /**
   * Adds the given map to the context provided that
   * all the keys in that map are of type String.
   *
   * All occurrences of "." in a key are replaced by "_",
   * since it is not possible to access keys containing dots
   * from a velocity template.
   *
   * The context is left unchanged, if <code>map</code>
   * is <code>null</code>.
   *
   * @throws ClassCastException if the key of the mapping is not
   *                            a string.
   * @czt.todo Insert strings containing a dot as a map into a
   *           velocity context?
   */
  public void addToContext(Map<String, ?> map)
  {
    final String methodName = "addToContext";
    LOGGER.entering(CLASS_NAME, methodName, map);

    if (map == null) {
      return;
    }
    
    for (Map.Entry<String, ?> entry : map.entrySet()) {
      String key = entry.getKey();
      key = key.replace('.', '_');
      Object value = entry.getValue();
      addToContext(key, value);
    }
    LOGGER.exiting(CLASS_NAME, methodName);
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
    LOGGER.entering(CLASS_NAME, methodName, name);
    context_.put(name, value);
    LOGGER.exiting(CLASS_NAME, methodName);
  }

  /**
   * Removes the mapping for this key from this map if it is present.
   *
   * @param key key whose mapping is to be removed from the map.
   */
  public Object removeFromContext(String key)
  {
    return context_.remove(key);
  }

  // **************** GENERATING TEXT/CODE **********************

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
    LOGGER.entering(CLASS_NAME, methodName);
    LOGGER.fine("Use template file " + template_ + ".");
    LOGGER.fine("Use context " + context_ + ".");
    LOGGER.fine("Use writer " + writer_ + ".");
    Template template = velocity_.getTemplate(template_);
    template.merge(context_, writer_);
    writer_.flush();

    LOGGER.exiting(CLASS_NAME, methodName);
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
   * @throws NullPointerException if the template is <code>null</code>.
   * @throws GnastException if there was a parse error in the
   *                        template file.
   */
  public boolean generate(Level level)
  {
    assert context_ != null : "Context is null.";
    assert writer_ != null : "Writer is null.";
    if (template_ == null) throw new NullPointerException();

    final String methodName = "generate";
    LOGGER.entering(CLASS_NAME, methodName);
    LOGGER.fine("Use template file " + template_ + ".");
    LOGGER.fine("Use context " + context_ + ".");
    LOGGER.fine("Use writer " + writer_ + ".");

    boolean success = false;
    try {
      generateLowLevel();
      success = true;
    }
    catch (ParseErrorException e) {
      throw new GnastException("Parse error in " + template_ + ".", e);
    }
    catch (ResourceNotFoundException e) {
      LOGGER.log(level, e.getMessage());
      e.printStackTrace();
      success = false;
    }
    catch (IOException e) {
      LOGGER.log(level, e.getMessage());
    }
    catch (Exception e) {
      LOGGER.log(level, "Cannot apply template file " + template_ + ".");
      LOGGER.log(level, "Caused by: " + e.getMessage());
      //      e.printStackTrace();
      success = false;
    }
    LOGGER.exiting(CLASS_NAME, methodName, new Boolean(success));
    return success;
  }

  // ############################################################
  // ##################### STATIC METHODS #######################
  // ############################################################

  /**
   * Returns a map from string to object containing all the entries
   * from <code>map</code> that start with <code>name</code> followed
   * by a dot. That is, a pair of a string <code>s</code> and an object
   * <code>o</code> is contained in the returned map if and only if
   * the string <code>name + "." + s</code> and the object <code>o</code>
   * is contained in <code>map</code>.
   *
   * @throws ClassCastException if one of the keys of the mapping
   *                            is not a string.
   * @throws NullPointerException if the map or the name is <code>null</code>.
   */
  public static Map<String,Object> parseMap(Map<Object,Object> map, String name)
  {
    final String methodName = "parseMap";
    LOGGER.entering(CLASS_NAME, methodName);

    Map<String,Object> erg = new HashMap<String,Object>();
    for (Map.Entry<Object,Object> entry : map.entrySet()) {
      String s = (String) entry.getKey();
      if (s.startsWith(name + ".")) {
        String key = s.substring(name.length() + 1, s.length());
        Object value = entry.getValue();
        erg.put(key, value);
      }
    }
    LOGGER.exiting(CLASS_NAME, methodName, erg);
    return erg;
  }

  // ************************* MAIN *****************************

  /**
   * The main method.
   */
  public static void main (String[] args)
    throws Exception
  {
    String usage = CLASS_NAME + " class options:\n";
    usage += "  -p, --prop <file> The property file.\n";
    usage += "  -t, --template <file> The template file.\n";
    usage += " [-c, --class <name> The class name.]\n";

    int i = 0;
    String propertyFile = null;
    String templateFile = null;
    String name = null;

    while (i < args.length && args[i].startsWith("-")) {
      String arg = args[i++];
      if (arg.equals("-p")
          || arg.equals("--prop")
          || arg.equals("-prop"))
      {
        if (i < args.length) {
          propertyFile = args[i++];
        }
        else {
          System.err.println(arg + " requires a file name.");
          System.err.println(usage);
          return;
        }
      }
      else if (arg.equals("-t")
               || arg.equals("--template")
               || arg.equals("-template"))
      {
        if (i < args.length) {
          templateFile = args[i++];
        }
        else {
          System.err.println(arg + " requires a file name.");
          System.err.println(usage);
          return;
        }
      }
      else if (arg.equals("-c")
                 || arg.equals("--class")
                 || arg.equals("-class"))
      {
        if (i < args.length) {
          name = args[i++];
        }
        else {
          System.err.println(arg + " requires a string.");
          System.err.println(usage);
          return;
        }
      }
    }
    if (i < args.length
        || propertyFile == null
        || templateFile == null)
    {
      System.err.println(usage);
      return;
    }

    Properties props = new Properties();
    FileInputStream fis = new FileInputStream(propertyFile);
    try {
      try {
        props.load(fis);
      } finally {
        fis.close();
      }
    }
    catch (Exception e) {
      System.err.println(e.getMessage());
    }

    Logger rootLogger = Logger.getLogger("");
    rootLogger.setLevel(Level.ALL);
    Handler handler = null;
    Handler[] h = rootLogger.getHandlers();
    for (i = 0; i < h.length; i++) {
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
      gen = new Apgen(templateFile, toPropertyMap(props));
    }
    else {
      gen = new Apgen(templateFile);
      gen.addToContext("class", parseMap(props, name));
    }
    gen.generate(Level.SEVERE);
  }
  
  public static Map<String, Object> toPropertyMap(Properties props) {
    Map<String, Object> map = new HashMap<String, Object>();
    
    for (String prop : props.stringPropertyNames()) {
      map.put(prop, props.getProperty(prop));
    }
    
    return map;
  }
}
