/*
  Copyright 2003, 2005, 2006, 2007, 2012 Petra Malik, Andrius Velykis
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

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.logging.Formatter;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.GnuParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

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

  /** The base directory of GnAST templates in the plugin */
  private static final String BASE_TEMPLATES_DIR = "/vm/";
  
  /**
   * The list of additional template paths (e.g. for extending templates).
   */
  private List<File> templatePaths_ = new ArrayList<File>();
  
  
  /**
   * The directory for ZML schema source files.
   *
   * <p>It can be set by using the command line option
   * <code>-s</code>.
   *
   * <p>Should never be <code>null</code>.
   */
  private String sourceDir_ = ".";
  
  /**
   * The generated project namespace.
   *
   * <p>It can be set by using the command line option
   * <code>-p</code>.
   *
   * <p>Should never be <code>null</code>.
   */
  private String projectNamespace_ = "http://czt.sourceforge.net/zml";

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
  
  private boolean addAstFinaliser_ = false;


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
  // ################### (NON-STATIC) METHODS ####################
  // ############################################################

  // ****************** ARGUMENT PARSING ************************

  /**
   * Parses the arguments from the command line.
   *
   * @return <code>true</code> if parsing was successful;
   *         <code>false</code> otherwise.
   * @throws NullPointerException if <code>args</code> is <code>null</code>.
   */
  @SuppressWarnings("static-access")
  private boolean parseArguments(String[] args)
  {
    
    Options argOptions = new Options();
    
    OptionGroup verboseOptions = new OptionGroup();
    verboseOptions.addOption(OptionBuilder.withLongOpt("verbose")
                                          .withDescription("Verbose; display verbose debugging messages")
                                          .create("v"));
    verboseOptions.addOption(OptionBuilder.withLongOpt("vverbose")
                                          .withDescription("Very verbose; more verbose debugging messages")
                                          .create("vv"));
    verboseOptions.addOption(OptionBuilder.withLongOpt("vvverbose")
                                          .withDescription("Very very verbose; even more verbose debugging messages")
                                          .create("vvv"));
    argOptions.addOptionGroup(verboseOptions);
    
    argOptions.addOption(OptionBuilder.withLongOpt("finalizers")
                                      .withDescription("Add AST finalisers. WARNING: ASTs will consume more memory!")
                                      .create("f"));
    
    argOptions.addOption(OptionBuilder.withArgName("dir")
                                      .hasArg()
                                      .withLongOpt("destination")
                                      .withDescription("Generated files go into this directory")
                                      .create("d"));
    
    argOptions.addOption(OptionBuilder.withArgName("dir1 dir2")
                                      .hasArgs()
                                      .withValueSeparator(',')
                                      .withLongOpt("templates")
                                      .withDescription("Additional template directories")
                                      .create("t"));
    
    argOptions.addOption(OptionBuilder.withArgName("dir")
                                      .hasArg()
                                      .withLongOpt("source")
                                      .withDescription("The directory with all ZML schema files. The requested project namespace must be present, as well as all its parents.")
                                      .create("s"));
    
    argOptions.addOption(OptionBuilder.withArgName("url")
                                      .hasArg()
                                      .withLongOpt("namespace")
                                      .withDescription("The namespace of the project to be generated.")
                                      .create("n"));
    
    // use GNU parser that allows longer option name (e.g. `-vvv`)
    CommandLineParser parser = new GnuParser();
    CommandLine line;
    try {
      // parse the command line arguments
      line = parser.parse(argOptions, args);
    }
    catch (ParseException exp) {
      // oops, something went wrong
      System.err.println(exp.getMessage());
      
      // automatically generate the help statement
      HelpFormatter formatter = new HelpFormatter();
      formatter.printHelp("gnast", argOptions, true);
      
      return false;
    }
    
    verbosity_ = line.hasOption("v") ? Level.INFO 
        : (line.hasOption("vv") ? Level.FINE 
            : (line.hasOption("vvv") ? Level.FINER 
                : Level.OFF));
    
    addAstFinaliser_ = line.hasOption("f");
    
    String dest = line.getOptionValue("d");
    if (dest != null) {
      destDir_ = dest;
    }
    
    String[] templates = line.getOptionValues("t");
    if (templates != null) {
      for (String path : templates) {
        templatePaths_.add(new File(path));
      }
    }
    
    String source = line.getOptionValue("s");
    if (source != null) {
      sourceDir_ = source;
    }
    
    String namespace = line.getOptionValue("n");
    if (namespace != null) {
      projectNamespace_ = namespace;
    }
    
    if (addAstFinaliser_) {
      defaultContext_.setProperty("addAstFinaliser", String.valueOf("1"));
    }
    
    if (verbosity_.intValue() < Level.INFO.intValue())
    {
      getLogger().log(Level.INFO, "GnAST context = {0}", defaultContext_.toString());
    }
    
    // TODO set verbosity?
    
    return true;
  }

  // ********************* OTHERS *************************

  /**
   * The main code generator method.
   * @param args 
   */
  public void generate(String[] args)
  {
    parseArguments(args);
    // handleLogging();

    try {
      
      // first resolve all schema projects from the indicated source directory
      // this is necessary to resolve transitive dependencies
      resolveProjects(sourceDir_);
      
      // now locate the required target project schema by its namespace
      Project targetProject = namespaces_.get(projectNamespace_);
      if (targetProject == null) {
        throw new GnastException("Cannot find schema with target namespace " + projectNamespace_
            + " in source directory " + sourceDir_);
      }
      
      // generate the ASTs
      targetProject.generate();
    }
    catch (RuntimeException e) {
      throw e;
    }
    catch (Exception e) {
      Throwable t = e;
      while (t != null) {
        if (t == e) getLogger().severe(t.getMessage());
        else getLogger().log(Level.SEVERE, "Caused by: {0}", t.getMessage());
        t = t.getCause();
      }
    }
  }
  
  private void resolveProjects(String sourceDir)
  {
    File sourceFile = new File(sourceDir);
    if (sourceFile.isDirectory()) {
      
      for (File schemaFile : sourceFile.listFiles()) {
        if (schemaFile.getName().endsWith(".xsd")) {
          Project project = getProject(schemaFile);
          namespaces_.put(project.getTargetNamespace(), project);
        }
      }
      
    } else {
      throw new GnastException("Invalid source directory: " + sourceFile);
    }
  }
  
  // ################ INTERFACE GlobalProperties ####################

  @Override
  public Project getProjectName(String namespace)
  {
    return namespaces_.get(namespace);
  }

  public Project getProject(URL url)
  {
    String name = url.toString();
    Project result = projects_.get(name);
    if (result == null) {
      result = new Project(url, this);
      projects_.put(name, result);
    }
    return result;
  }
  
  private Project getProject(File file)
  {
    try {
      URL url = file.toURI().toURL();
      return getProject(url);
    }
    catch (MalformedURLException e) {
      throw new GnastException(e);
    }
  }

  @Override
  public Properties getDefaultContext()
  {
    return defaultContext_;
  }

  @Override
  public String toDirectoryName(String packageName)
  {
    return destDir_
      + File.separatorChar
      + packageName.replace('.', File.separatorChar)
      + File.separatorChar;
  }

  @Override
  public String toFileName(String packageName, String className)
  {
    return toDirectoryName(packageName)
      + className
      + ".java";
  }

  @Override
  public String getBaseDir()
  {
    return BASE_TEMPLATES_DIR;
  }
  
  @Override
  public List<File> getTemplatePaths()
  {
    return templatePaths_;
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
   * @param name the file to be read.
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
            getLogger().log(Level.WARNING, "Cannot read property resource {0}", name);
          }
        }
        else {
          getLogger().log(Level.WARNING, "Cannot find property file {0}", name);
        }
      }
      catch (java.io.IOException ioe) {
        getLogger().log(Level.WARNING, "Cannot read property file {0}", name);
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
   * @param prefix 
   * @param props 
   * @return should never be <code>null</code>.
   */
  public static Properties removePrefix(String prefix, Properties props)
  {
    Properties result = new Properties();
    for (Enumeration<?> e = props.propertyNames(); e.hasMoreElements();) {
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
   * @param prefix 
   * @param props 
   * @return should never be <code>null</code>.
   */
  public static Properties withPrefix(String prefix, Properties props)
  {
    Properties result = new Properties();
    for (Enumeration<?> e = props.propertyNames(); e.hasMoreElements();) {
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
   * @param args 
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
    @Override
    public String format(LogRecord record)
    {
      return record.getLevel().toString()
        + ": "
        + record.getMessage()
        + "\n";
    }
  }
}
