/*
  Copyright 2003, 2005, 2006, 2007, 2012  Petra Malik, Andrius Velykis
  
  This file is part of the CZT project.

  The CZT project is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT.  If not, see <http://www.gnu.org/licenses/>.
*/

package net.sourceforge.czt.gnast;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
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
import org.sonatype.plexus.build.incremental.BuildContext;
import org.sonatype.plexus.build.incremental.DefaultBuildContext;

import static net.sourceforge.czt.gnast.ResourceUtils.getURLChanges;

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
  
  private static final String DESTINATION_DEFAULT = ".";
  private static final Boolean AST_FINALISER_DEFAULT = Boolean.FALSE;
  private static final String MAPPING_FILE_DEFAULT = "mapping.properties";
  
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
  
  private Properties mapping = new Properties();
  
  private Set<String> changedBuildFiles = new HashSet<String>();
  
  private boolean forceGenerateAll = true;
  
  /**
   * A cache for path resolution. Needed because checking if file name exists
   * can be an expensive operation - hopefully the cache can help somewhat.
   */
  private final Map<String, Boolean> pathResolvedCache = new HashMap<String, Boolean>();


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
    Properties gnastProperties = loadProperties(findResource(PROPERTY_FILE));

    if (config.destination == null) {
      // try reading from the properties
      // otherwise use the default - local dir "."
      config.destination = new File(gnastProperties.getProperty("dest.dir", DESTINATION_DEFAULT));
    }
    defaultContext_ = removePrefix("vm.", gnastProperties);
    
    if (config.addAstFinalizer == null) {
      // check if there is a property set for the finaliser, then convert it to Boolean
      // e.g. it may be "false" as a String
      Object astFinaliserVal = defaultContext_.get(AST_FINALISER_PROP);
      if (astFinaliserVal instanceof String) {
        config.addAstFinalizer = Boolean.parseBoolean((String) astFinaliserVal);
      } else {
        // use default
        config.addAstFinalizer = AST_FINALISER_DEFAULT;
      }
    }
    
    // put the property into context
    defaultContext_.put(AST_FINALISER_PROP, config.addAstFinalizer);
    
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
    
    argOptions.addOption(OptionBuilder.withArgName("file")
                                      .hasArg()
                                      .withLongOpt("mapping")
                                      .withDescription("XML type mapping properties file")
                                      .create("m"));
    
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
    List<URL> templateDirs = new ArrayList<URL>();
    for (String path : templates) {
      templateDirs.add(toURL(path));
    }
    
    return new GnastBuilder()
      .verbosity(verbosity)
      .finalizers(line.hasOption("f"))
      .destination(toFile(line.getOptionValue("d")))
      .templates(templateDirs)
      .mapping(toURL(line.getOptionValue("m")))
      .sourceSchemas(schemaDirToURL(line.getOptionValue("s")))
      .namespace(line.getOptionValue("n"));
  }
  
  private static File toFile(String path)
  {
    if (path == null) {
      return null;
    }
    else {
      return new File(path);
    }
  }
  
  private static URL toURL(String path)
  {
    return toURL(toFile(path));
  }

  private static URL toURL(File file)
  {
    if (file == null) {
      return null;
    }
    
    try {
      return file.toURI().toURL();
    }
    catch (MalformedURLException e) {
      throw new GnastException("File " + file + " cannot be converted to URL: " + e.getMessage(), e);
    }
  }
  
  private static Collection<URL> schemaDirToURL(String path) {
    return schemaDirToURL(path != null ? new File(path) : null);
  }
  
  public static Collection<URL> schemaDirToURL(File dir) {
    
    if (dir == null) {
      return Collections.emptySet();
    }
    
    Set<URL> fileUrls = new HashSet<URL>();
    File[] listFiles = dir.listFiles();
    if (listFiles != null)
    {
	    for (File file : listFiles) {
	      if (file.getName().endsWith(".xsd")) {
	        fileUrls.add(toURL(file));
	      }
	    }
    }
    else
    {
    	throw new IllegalArgumentException("Couldn't get list of files for given path " + dir.getName());
    }
    return fileUrls;
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
      
      if (config.mappingPropertiesFile == null) {
        config.mappingPropertiesFile = findResource(MAPPING_FILE_DEFAULT);
      }
      
      // generate all if the source schemas have changed, destination does not exist,
      // or mapping has changed, or the build is not incremental
      boolean generateAll = !config.buildContext.isIncremental()
          || sourceSchemasChanged(config.sourceSchemas) 
          || !config.destination.exists()
          || !getURLChanges(config.buildContext, config.mappingPropertiesFile, false).isEmpty();
      
      Set<String> changedBuildFiles = new HashSet<String>();
      if (!generateAll) {
        // check if the templates have changed
        for (URL templatePath : getTemplatePaths()) {
          changedBuildFiles.addAll(getURLChanges(config.buildContext, templatePath, true));
        }
        
// Avoid checking the destination for now - incremental build loops because /target is refreshed
//        // also check destination for changes
//        if (config.destination.exists()) {
//          changedBuildFiles.addAll(getDirChanges(config.destination));
//        }
      }
      
      if (!generateAll && changedBuildFiles.isEmpty()) {
        // source schemas, template paths and build directory is up-to-date
        // no need to regenerate, so stop now
        return;
      }
      
      this.forceGenerateAll = generateAll;
      this.changedBuildFiles = Collections.unmodifiableSet(changedBuildFiles);
      
      if (config.mappingPropertiesFile != null) {
        this.mapping = loadProperties(config.mappingPropertiesFile);
      }
      
      // first resolve all schema projects from the indicated source directory
      // this is necessary to resolve transitive dependencies
      resolveProjects(config.sourceSchemas);
      
      // now locate the required target project schema by its namespace
      Project targetProject = namespaces_.get(config.namespace);
      if (targetProject == null) {
        throw new GnastException("Cannot find schema with target namespace " + config.namespace
            + " in given locations " + config.sourceSchemas);
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
  
  private void resolveProjects(Collection<URL> sourceSchemas)
  {
    for (URL schemaUrl : sourceSchemas) {
      Project project = getProject(schemaUrl);
      namespaces_.put(project.getTargetNamespace(), project);
    }
  }
  
  private boolean sourceSchemasChanged(Collection<URL> sourceSchemas)
  {
    for (URL schemaUrl : sourceSchemas) {
      if (!getURLChanges(config.buildContext, schemaUrl, false).isEmpty()) {
        return true;
      }
    }
    
    return false;
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
      result = new Project(url, mapping, this);
      projects_.put(name, result);
    }
    return result;
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
  public List<URL> getTemplatePaths()
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
  public boolean forceGenerateAll()
  {
    return forceGenerateAll;
  }
  
  /**
   * Resolves the given template file in one of the template directories (checks if it exists).
   * 
   * @param fileName
   * @return
   */
  @Override
  public String resolvePath(String fileName)
  {
    
    Boolean cachedResolved = pathResolvedCache.get(fileName);
    if (cachedResolved != null) {
      
      if (cachedResolved.booleanValue()) {
        // cached and resolvable
        return fileName;
      } else {
        // cached, but not resolvable 
        return null;
      }
    }
    
    // not cached - try resolving
    boolean resolved = canResolvePath(fileName);
    // cache
    pathResolvedCache.put(fileName, resolved);
    
    return resolved ? fileName : null;
  }
  
  private boolean canResolvePath(String fileName) {
    // check if file exists somewhere in template paths
    for (URL templatePath : getTemplatePaths()) {
      
      URL fileUrl;
      try {
        fileUrl = new URL(templatePath.toString() + "/" + fileName);
      }
      catch (MalformedURLException e) {
        throw new GnastException(e);
      }
      
      File file = ResourceUtils.getFile(fileUrl);
      if (file != null) {
        if (file.exists()) {
          return true;
        }
      } else {
        // try opening a stream to see whether it is a valid URL
        
        try {
          InputStream testStream = fileUrl.openStream();
          testStream.close();
          return true;
        }
        catch (IOException e) {
          // ignore - cannot open a stream, so file does not exist
        }
      }
    }
    
    // not found
    return false;
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
   * Returns the URL of the given resource file.
   * <p>
   * First, the current working directory is tried, then the name is treated as a resource.
   * If the given file cannot be found, {@code null} is returned.
   * </p>
   * 
   * @param name the file to be located.
   * @return the URL of the resource file, or {@code null} if not found.
   */
  private static URL findResource(String name)
  {
    if (name == null) {
      return null;
    }
    
    File file = new File(name);
    if (file.exists()) {
      return toURL(file);
    } else {
      URL resourceUrl = Gnast.class.getResource("/" + name);
      if (resourceUrl == null) {
        getLogger().log(Level.WARNING, "Cannot find resource " + name);
      }
      return resourceUrl;
    }
  }

  /**
   * Returns the properties provided in the given URL.
   * <p>
   * If the given file cannot be found or read, logging messages are written and the empty property
   * map is returned. This means that the caller cannot distinguish whether an attempt to read a
   * file was unsuccessful or the file did not contain properties.
   * </p>
   * 
   * @param url the URL of a file to be read.
   * @return the properties contained in the file or the
   *         empty property mapping (should never be {@code null}).
   */
  private static Properties loadProperties(URL url)
  {
    final String methodName = "loadProperties";
    getLogger().entering(getClassName(), methodName, url);
    
    Properties erg = new Properties();
    
    if (url != null) {
      InputStream urlStream = null;
      try {
        urlStream = url.openStream();
        erg.load(urlStream);
      }
      catch (IOException e) {
        getLogger().log(Level.WARNING, "Cannot read property resource at " + url, e);
      } finally {
        if (urlStream != null) {
          try {
            urlStream.close();
          }
          catch (IOException e) {
            getLogger().log(Level.WARNING, "Cannot close property resource at " + url, e);
          }
        }
      }
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
    
    private Boolean addAstFinalizer = null;
    
    /**
     * The destination directory where all the generated files go in.
     */
    private File destination = null;
    
    /**
     * The list of additional template paths (e.g. for extending templates).
     */
    private List<URL> templatePaths = new ArrayList<URL>();
    
    /**
     * The mapping properties file.
     */
    private URL mappingPropertiesFile = null;
    
    /**
     * XML schema source files from which to generate ASTs.
     */
    private Set<URL> sourceSchemas = Collections.emptySet();
    
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
      }
      return this;
    }
    
    public GnastBuilder mapping(URL mappingPropertiesFile) {
      if (mappingPropertiesFile != null) {
        this.mappingPropertiesFile = mappingPropertiesFile;
      }
      return this;
    }
    
    public GnastBuilder templates(List<URL> templatePaths) {
      this.templatePaths.addAll(templatePaths);
      return this;
    }
    
    public GnastBuilder sourceSchemas(Collection<URL> sourceSchemas) {
      this.sourceSchemas = new HashSet<URL>(sourceSchemas);
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
