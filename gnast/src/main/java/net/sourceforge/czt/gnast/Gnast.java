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
import java.util.Arrays;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
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
import org.codehaus.plexus.util.Scanner;
import org.sonatype.plexus.build.incremental.BuildContext;
import org.sonatype.plexus.build.incremental.DefaultBuildContext;

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
 * @author Andrius Velykis
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
  
  private static final String AST_FINALISER_PROP = "addAstFinaliser";

  /**
   * <p>
   * Project independent settings intended to be used
   * within the generated code.
   * Examples are settings for author, copyright, etc.
   * </p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Map<String, Object> defaultContext_;

  /**
   * <p>A mapping from namespaces (used in schema files)
   * to projects.</p>
   *
   * <p>Should never be <code>null</code>.
   */
  private Map<String,Project> namespaces_ = new HashMap<String,Project>();


  /** The base directory of GnAST templates in the plugin */
  private static final String BASE_TEMPLATES_DIR = "/vm/";
  
  
  /**
   * <p>A mapping from project names to the actual projects.</p>
   *
   * <p>If {@link #getProject} is called, first this map is
   * tried to obtain the project. If no entry for the given
   * name is found, a new project is created and added to this map.
   * </p>
   */
  private Map<String,Project> projects_ = new HashMap<String,Project>();
  
  private final GnastBuilder config;
  
  private Set<String> changedBuildFiles = new HashSet<String>();
  
  private boolean schemaChanged = true;


  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * Constructs a new gnast code generator and initialises its
   * member variables by reading the gnast properties file
   * named {@link #PROPERTY_FILE}.
   */
  private Gnast(GnastBuilder config)
  {
    Properties gnastProperties = loadProperties(PROPERTY_FILE);

    if (!config.destinationSet) {
      // try reading from the properties
      config.destination = new File(gnastProperties.getProperty("dest.dir", config.destination.getPath()));
    }
    defaultContext_ = removePrefix("vm.", gnastProperties);
    
    if (config.addAstFinalizer) {
      defaultContext_.put(AST_FINALISER_PROP, Boolean.TRUE);
    } else {
      // check if there is a property set for the finaliser, then convert it to Boolean
      // e.g. it may be "false" as a String
      Object astFinaliserVal = defaultContext_.get(AST_FINALISER_PROP);
      if (astFinaliserVal instanceof String) {
        defaultContext_.put(AST_FINALISER_PROP, Boolean.parseBoolean((String) astFinaliserVal));
      }
    }
    
    if (config.verbosity.intValue() < Level.INFO.intValue())
    {
      getLogger().log(Level.INFO, "GnAST context = {0}", defaultContext_.toString());
    }
    
    // TODO set verbosity?
    
    this.config = config;
  }

  // ############################################################
  // ################### (NON-STATIC) METHODS ####################
  // ############################################################

  // ****************** ARGUMENT PARSING ************************

  /**
   * Parses the arguments from the command line.
   *
   * @return a configured GnAST builder if parsing was successful;
   *         {@code null} otherwise.
   * @throws NullPointerException if {@code args} is {@code null}
   */
  @SuppressWarnings("static-access")
  private static GnastBuilder parseArguments(String[] args)
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
      
      return null;
    }
    
    Level verbosity = line.hasOption("v") ? Level.INFO 
        : (line.hasOption("vv") ? Level.FINE 
            : (line.hasOption("vvv") ? Level.FINER 
                : Level.OFF));
    
    String[] templates = line.getOptionValues("t");
    List<File> templateDirs = new ArrayList<File>();
    for (String path : templates) {
      templateDirs.add(new File(path));
    }
    
    return new GnastBuilder()
      .verbosity(verbosity)
      .finalizers(line.hasOption("f"))
      .destination(toFile(line.getOptionValue("d")))
      .templates(templateDirs)
      .source(toFile(line.getOptionValue("s")))
      .namespace(line.getOptionValue("n"));
  }
  
  private static File toFile(String path) {
    if (path == null) {
      return null;
    } else {
      return new File(path);
    }
  }

  // ********************* OTHERS *************************

  /**
   * The main code generator method.
   * @param args 
   */
  public void generate()
  {
    // handleLogging();

    try {
      
      boolean projectsChanged = !resolveProjectFiles(config.source, false).isEmpty();
      boolean needToGenerate = projectsChanged;
      Set<String> changedBuildFiles = new HashSet<String>();
      if (!projectsChanged) {
        // check if the templates have changed
        
        // get the base dir - may be in JAR!
        File baseDir = Project.getFile(Project.getBaseDirResource(this, ""));
        if (baseDir != null) {
          // base dir can be resolved and is not in a JAR - check for changes
          changedBuildFiles.addAll(getDirChanges(baseDir));
        }
        
        // check other template paths for changes
        for (File templatePath : getTemplatePaths()) {
          changedBuildFiles.addAll(getDirChanges(templatePath));
        }
        
// Avoid checking the destination for now - incremental build loops because /target is refreshed
//        // also check destination for changes
//        if (config.destination.exists()) {
//          changedBuildFiles.addAll(getDirChanges(config.destination));
//        }
        
        needToGenerate = !changedBuildFiles.isEmpty();
      }
      
      if (!needToGenerate) {
        // source schemas, template paths and build directory is up-to-date
        // no need to regenerate, so stop now
        return;
      }
      
      this.schemaChanged = projectsChanged;
      this.changedBuildFiles = Collections.unmodifiableSet(changedBuildFiles);
      
      // first resolve all schema projects from the indicated source directory
      // this is necessary to resolve transitive dependencies
      resolveProjects(config.source);
      
      // now locate the required target project schema by its namespace
      Project targetProject = namespaces_.get(config.namespace);
      if (targetProject == null) {
        throw new GnastException("Cannot find schema with target namespace " + config.namespace
            + " in source directory " + config.source);
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
  
  private void resolveProjects(File sourceDir)
  {
    // ignore changes - take all project files
    List<File> allProjectFiles = resolveProjectFiles(sourceDir, true);
    
    for (File schemaFile : allProjectFiles) {
      Project project = getProject(schemaFile);
      namespaces_.put(project.getTargetNamespace(), project);
    }
  }
  
  private List<File> resolveProjectFiles(File sourceDir, boolean ignoreDelta)
  {
    Scanner scanner = config.buildContext.newScanner(sourceDir, ignoreDelta);
    scanner.setIncludes(new String[]{"*.xsd"});
    scanner.scan();

    String[] includedFiles = scanner.getIncludedFiles();
    List<File> projectFiles = new ArrayList<File>();
    for (String schemaFile : includedFiles) {
      projectFiles.add(new File(sourceDir + "/" + schemaFile));
    }

    return projectFiles;
  }
  
  private Set<String> getDirChanges(File dir) {
    
    Set<String> dirChanges = new HashSet<String>();
    
    Scanner deleteScanner = config.buildContext.newDeleteScanner(dir);
    deleteScanner.scan();
    dirChanges.addAll(Arrays.asList(deleteScanner.getIncludedFiles()));
    
    Scanner changeScanner = config.buildContext.newScanner(dir);
    changeScanner.scan();
    dirChanges.addAll(Arrays.asList(changeScanner.getIncludedFiles()));
    
    // also add full paths
    Set<String> dirChangesFullPaths = new HashSet<String>();
    for (String relative : dirChanges) {
      dirChangesFullPaths.add(dir + "/" + relative);
    }
    dirChanges.addAll(dirChangesFullPaths);
    
    return dirChanges;
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
  public Map<String, ?> getDefaultContext()
  {
    return defaultContext_;
  }

  @Override
  public String toDirectoryName(String packageName)
  {
    return config.destination.getPath()
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
    return config.templatePaths;
  }
  
  @Override
  public BuildContext getBuildContext()
  {
    return config.buildContext;
  }
  
  @Override
  public Set<String> getChangedFiles()
  {
    return changedBuildFiles;
  }
  
  @Override
  public boolean isSchemaChanged()
  {
    return schemaChanged;
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
  public static Map<String, Object> removePrefix(String prefix, Properties props)
  {
    Map<String, Object> result = new HashMap<String, Object>();
    for (String prop : props.stringPropertyNames()) {
      if (prop.startsWith(prefix)) {
        result.put(prop.substring(prefix.length()), props.getProperty(prop));
      }
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
    GnastBuilder config = parseArguments(args);
    if (config != null) {
      config.create().generate();
    }
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
  
  public static class GnastBuilder {
    
    /**
     * The verbosity used for logging to stdout.
     */
    private Level verbosity = Level.SEVERE;
    
    private boolean addAstFinalizer = false;
    
    /**
     * The destination directory where all the generated files go in.
     */
    private File destination = new File(".");
    private boolean destinationSet = false;
    
    /**
     * The list of additional template paths (e.g. for extending templates).
     */
    private List<File> templatePaths = new ArrayList<File>();
    
    /**
     * The directory for ZML schema source files.
     */
    private File source = new File(".");
    
    /**
     * The generated project namespace.
     */
    private String namespace = "http://czt.sourceforge.net/zml";
    
    /**
     * The build context to read/write to filesystem.
     * By default, use non-incremental build context.
     */
    private BuildContext buildContext = new DefaultBuildContext();
    
    
    public GnastBuilder verbosity(Level verbosity) {
      this.verbosity = verbosity;
      return this;
    }
    
    public GnastBuilder destination(File destination) {
      if (destination != null) {
        this.destination = destination;
        this.destinationSet = true;
      }
      return this;
    }
    
    public GnastBuilder templates(List<File> templatePaths) {
      this.templatePaths.addAll(templatePaths);
      return this;
    }
    
    public GnastBuilder source(File source) {
      if (source != null) {
        this.source = source;
      }
      return this;
    }
    
    public GnastBuilder namespace(String namespace) {
      if (namespace != null) {
        this.namespace = namespace;
      }
      return this;
    }
    
    public GnastBuilder finalizers(boolean addAstFinalizer) {
      this.addAstFinalizer = addAstFinalizer;
      return this;
    }
    
    public GnastBuilder buildContext(BuildContext buildContext) {
      this.buildContext = buildContext;
      return this;
    }
    
    public Gnast create() {
      return new Gnast(this);
    }
    
  }
}
