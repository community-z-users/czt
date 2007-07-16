/*
  Copyright 2003, 2005, 2006, 2007 Petra Malik
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
import java.net.URL;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Properties;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.LogRecord;

import net.sourceforge.czt.zml.Resources;

/**
 * <p>The GnAST command line user interface.</p>
 *
 * <p>
 * This class contains the main method for calling the AST code generator.
 * It parses all user settings
 * (provided via the gnast properties file and command line options)
 * and makes these settings available to other objects.
 * </p>
 *
 * @author Petra Malik
 */
public class Gnast implements GlobalProperties
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  /**
   * The location of the gnast properties file.
   */
  private static final String PROPERTY_FILE = "gnast.properties";

  /**
   * <p>
   * Project independent settings intended to be used
   * within the generated code.
   * Examples are settings for author, copyright, etc.
   * </p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Properties defaultContext_;

  /**
   * <p>A mapping from namespaces (used in schema files)
   * to projects.</p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Map<String,Project> namespaces_ = new HashMap<String,Project>();

  /**
   * <p>The destination directory
   * where all the generated files go in.</p>
   *
   * <p>It can be set by setting property dest.dir in the
   * gnast properties file or by using the command line option
   * <code>-d</code>.
   *
   * <p>Should never be <code>null</code>.
   */
  private String destDir_ = ".";

  /**
   * <p>The base directory</p>
   *
   * <p>It can be set by using the command line option
   * <code>-b</code>.
   *
   * <p>Should never be <code>null</code>.
   */
  private String baseDir_ = ".";

  /**
   * <p>A mapping from project names to the actual projects.</p>
   *
   * <p>If {@link #getProject} is called, first this map is
   * tried to obtain the project. If no entry for the given
   * name is found, a new project is created and added to this map.
   * </p>
   */
  private Map<String,Project> projects_ = new HashMap<String,Project>();

  /**
   * The verbosity used for logging to stdout.
   */
  private Level verbosity_ = Level.SEVERE;


  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * Constructs a new gnast code generator and initialises its
   * member variables by reading the gnast properties file
   * named {@link #PROPERTY_FILE}.
   */
  public Gnast()
  {
    Properties gnastProperties = loadProperties(PROPERTY_FILE);

    destDir_ = gnastProperties.getProperty("dest.dir", destDir_);
    defaultContext_ = removePrefix("vm.", gnastProperties);
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ****************** ARGUMENT PARSING ************************

  /**
   * Prints usage information to stdout.
   */
  private void printUsage()
  {
    System.out.println("class options (all arguments are optional):\n"
      + "  -d <dir>  Generated files go into this directory\n"
      + "  -p <name> The name of the project to be generated\n"
      + "  -v        Verbose; display verbose debugging messages\n");
  }

  /**
   * Prints the given message followed by usage information
   * for the gnast code generator to stdout.
   */
  private void printUsageMessage(String message)
  {
    System.out.println(message);
    printUsage();
  }

  /**
   * Parses the arguments from the command line.
   *
   * @return <code>true</code> if parsing was successful;
   *         <code>false</code> otherwise.
   * @throws NullPointerException if <code>args</code> is <code>null</code>.
   */
  private boolean parseArguments(String[] args)
  {
    int i = 0;
    while (i < args.length && args[i].startsWith("-")) {
      String arg = args[i++];
      if (arg.equals("-v")) verbosity_ = Level.INFO;
      else if (arg.equals("-vv")) verbosity_ = Level.FINE;
      else if (arg.equals("-vvv")) verbosity_ = Level.FINER;
      else if (arg.equals("-d")) {
        if (i < args.length) {
          destDir_ = args[i++];
        }
        else {
          printUsageMessage(arg + " requires a directory name");
          return false;
        }
      }
      else if (arg.equals("-b")) {
        if (i < args.length) {
          baseDir_ = args[i++];
        }
        else {
          printUsageMessage(arg + " requires a directory name");
          return false;
        }
      }
    }
    if (i < args.length) {
      printUsageMessage("Parse error at " + args[i]);
      return false;
    }
    return true;
  }

  // ********************* LOGGING *************************

  private void handleLogging()
  {
    Logger rootLogger = Logger.getLogger("");
    rootLogger.setLevel(Level.FINEST);

    // setting console logger
    Handler handler = null;
    Handler[] h = rootLogger.getHandlers();
    for (int i = 0; i < h.length; i++) {
      if (h[i] instanceof ConsoleHandler) {
        handler = h[i];
      }
    }
    if (handler == null) {
      handler = new ConsoleHandler();
      rootLogger.addHandler(handler);
    }
    handler.setLevel(verbosity_);
    handler.setFormatter(new OutputFormatter());

    // setting file logger
    try {
      handler = new FileHandler("gnast.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
    }
    catch (Exception e) {
      getLogger().severe(e.getMessage());
    }
    rootLogger.addHandler(handler);
  }

  // ********************* OTHERS *************************

  /**
   * The main code generator method.
   */
  public void generate(String[] args)
  {
    parseArguments(args);
    // handleLogging();

    try {
      // The order here must respect dependencies!
      generate(Resources.getZSchema());
      generate(Resources.getZpattSchema());
      generate(Resources.getOzSchema());
      generate(Resources.getCircusSchema());
      generate(Resources.getCircusPattSchema());
    }
    catch (RuntimeException e) {
      throw e;
    }
    catch (Exception e) {
      Throwable t = e;
      while (t != null) {
        if (t == e) getLogger().severe(t.getMessage());
        else getLogger().severe("Caused by: " + t.getMessage());
        t = t.getCause();
      }
      return;
    }
  }

  private void generate(URL url)
    throws Exception
  {
    Project project = getProject(url);
    namespaces_.put(project.getTargetNamespace(), project);
    project.generate();
  }

  // ################ INTERFACE GlobalProperties ####################

  public Project getProjectName(String namespace)
  {
    return namespaces_.get(namespace);
  }

  public Project getProject(URL url)
  {
    String name = url.toString();
    Project result = (Project) projects_.get(name);
    if (result == null) {
      result = new Project(url, this);
      projects_.put(name, result);
    }
    return result;
  }

  public Properties getDefaultContext()
  {
    return defaultContext_;
  }

  public String toDirectoryName(String packageName)
  {
    return destDir_
      + File.separatorChar
      + packageName.replace('.', File.separatorChar)
      + File.separatorChar;
  }

  public String toFileName(String packageName, String className)
  {
    return toDirectoryName(packageName)
      + className
      + ".java";
  }

  public String getBaseDir()
  {
    return baseDir_;
  }

  // ############################################################
  // ##################### STATIC METHODS #######################
  // ############################################################

  // ********************** LOGGING *****************************

  /**
   * Returns the class name of this class
   * (used for logging purposes).
   */
  private static String getClassName()
  {
    return "Gnast";
  }

  /**
   * Returns the logger used when logging information is provided.
   */
  private static Logger getLogger()
  {
    String packageName = "net.sourceforge.czt.gnast";
    return Logger.getLogger(packageName + "." + getClassName());
  }

  /**
   * Returns the properties provided in the given file.
   * First, the current working directory is tried,
   * then the name is treated as a resource.
   * If the given file cannot be found or read, logging
   * messages are written and the empty property map is
   * returned.  This means that the caller cannot distinguish
   * whether an attempt to read a file was unseccessful or
   * the file did not contain properties.
   *
   * @param filename the file to be read.
   * @return the properties contained in the file or the
   *         empty property mapping (should never be
   *         <code>null</code>).
   */
  public static Properties loadProperties(String name)
  {
    final String methodName = "loadProperties";
    getLogger().entering(getClassName(), methodName, name);
    Properties erg = new Properties();
    if (name != null) {
      try {
        erg.load(new FileInputStream(name));
      }
      catch (FileNotFoundException fnfe) {
        URL url = Gnast.class.getResource("/" + name);
        if (url != null) {
          try {
            erg.load(url.openStream());
          }
          catch (java.io.IOException ioe) {
            getLogger().warning("Cannot read property resource " + name);
          }
        }
        else {
          getLogger().warning("Cannot find property file " + name);
        }
      }
      catch (java.io.IOException ioe) {
        getLogger().warning("Cannot read property file " + name);
      }
    }
    if (name != null) {
    }
    getLogger().exiting(getClassName(), methodName, erg);
    return erg;
  }

  /**
   * Returns a property list of all the properties in <code>props</code>
   * that start with the given <code>prefix</code>, but with the prefix
   * removed. That is, a property named Foo is in the returned property
   * list if and only if the value of <code>prefix</code> concatenated
   * with Foo is contained in <code>props</code>. Furthermore, the values
   * of both properties are equal.
   *
   * @return should never be <code>null</code>.
   */
  public static Properties removePrefix(String prefix, Properties props)
  {
    Properties result = new Properties();
    for (Enumeration e = props.propertyNames(); e.hasMoreElements();) {
      String propertyName = (String) e.nextElement();
      if (propertyName.startsWith(prefix))
        result.setProperty(propertyName.substring(prefix.length()),
                           props.getProperty(propertyName));
    }
    return result;
  }

  /**
   * Returns a property list of all the properties in <code>props</code>
   * that start with the given <code>prefix</code>.
   * Furthermore, the values of both properties are equal.
   *
   * @return should never be <code>null</code>.
   */
  public static Properties withPrefix(String prefix, Properties props)
  {
    Properties result = new Properties();
    for (Enumeration e = props.propertyNames(); e.hasMoreElements();) {
      String propertyName = (String) e.nextElement();
      if (propertyName.startsWith(prefix))
        result.setProperty(propertyName,
                           props.getProperty(propertyName));
    }
    return result;
  }

  /**
   * The main method.  See #printUsage to see
   * how to use this method.
   */
  public static void main (String[] args)
  {
    Gnast gen = new Gnast();
    gen.generate(args);
  }

  // ############################################################
  // ##################### INNER CLASSES ########################
  // ############################################################

  /**
   * The output formatter that provides a nice output
   * using the logging messages.
   */
  class OutputFormatter extends  Formatter
  {
    public String format(LogRecord record)
    {
      return record.getLevel().toString()
        + ": "
        + record.getMessage()
        + "\n";
    }
  }
}
