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

import net.sourceforge.czt.gnast.schema.SchemaProject;

/**
 * <p>The Gnast command line user interface.</p>
 *
 * <p>This class contains the main method for calling the
 * AST code generator.  It is the glue that holds all
 * together: knows how to call the XML schema parser
 * as well as the code generator and handles the information flow
 * between them.</p>
 *
 * @author Petra Malik
 */
public class Gnast
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  /**
   * The class name of this class; used for logging purposes.
   */
  private static final String sClassName = "Gnast";

  /**
   * The logger used when logging information is provided.
   */
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast" + "." + sClassName);

  /**
   * The code generator used for generating the files.
   */
  private Apgen mApgen;

  /**
   * Contains all the settings for the classes
   * to be generated.
   */
  private Properties mAstProperties = null;

  /**
   * The destination directory
   * where all the generated files go in.
   */
  private String mDestDir = null;

  /**
   * <p>The gnast properties file.</p>
   *
   * <p>Should never be <code>null</code>.
   *
   * @see #parseArguments
   */
  private String mGnastPropertyFile = "gnast.properties";

  /**
   * <p>The mapping properties.
   * They contain information of how XML schema types are
   * mapped to java types.</p>
   *
   * <p>Should never be <code>null</code>.</p>
   */
  private Properties mMapping = new Properties();

  /**
   * The XML schema file used to compute
   * the AST classes.
   */
  private String mSchemaFile = null;

  /**
   * The verbosity used for logging to stdout.
   */
  private Level mVerbosity = Level.SEVERE;

  /**
   * @czt.todo This should go somewhere else.
   */
  private Properties mJavadoc = new Properties();



  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * Constructs a new gnast code generator.
   */
  public Gnast()
  {
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ****************** ARGUMENT PARSING ************************

  /**
   * Prints usage information for the gnast code generator
   * to stdout.
   */
  private void printUsage()
  {
    System.out.println("class options (all arguments are optional):\n"
      + "  -d <dir>  Generated files go into this directory\n"
      + "  -p <file> The gnast property file\n"
      + "  -s <file> The XML schema file used to compute the AST classes\n"
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
      if (arg.equals("-v")) mVerbosity = Level.INFO;
      else if (arg.equals("-vv")) mVerbosity = Level.FINE;
      else if (arg.equals("-vvv")) mVerbosity = Level.FINER;
      else if (arg.equals("-d"))
      {
	if (i < args.length)
	  mDestDir = args[i++];
	else {
	  printUsageMessage(arg + " requires a directory name");
	  return false;
	}
      }
      else if (arg.equals("-p"))
      {
	if (i < args.length)
	  mGnastPropertyFile = args[i++];
	else {
	  printUsageMessage(arg + " requires a file name");
	  return false;
	}
      }
      else if (arg.equals("-s"))
      {
	if (i < args.length)
	  mSchemaFile = args[i++];
	else {
	  printUsageMessage(arg + " requires a file name");
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

  // ********************* INITIALISING *************************

  /**
   * <p>Parses the gnast properties file and sets member variables
   * whos value is <code>null</code> according to the values
   * in the property file.</p>
   *
   * <p>Performs some checks whether all neccessary information was
   * provided.  If some information is missing, a message is written
   * and <code>false</code> is returned.
   * </p>
   *
   * @return <code>true</code> if the initialisation was successful;
   *         <code>false</code> otherwise.
   */
  private boolean init()
  {
    Properties gnastProperties =
      loadProperties(mGnastPropertyFile);
    if (mDestDir == null)
      mDestDir = gnastProperties.getProperty("dest.dir");
    if (mSchemaFile == null)
      mSchemaFile = gnastProperties.getProperty("schema.file");

    String mappingFile = gnastProperties.getProperty("mapping.file");
    mMapping = loadProperties(mappingFile);

    if (mDestDir == null) {
      printUsageMessage("Please provide a destination directory");
      return false;
    }
    if (mSchemaFile == null) {
      printUsageMessage("Please provide an XML schema file");
      return false;
    }

    mAstProperties = gnastProperties;
    return true;
  }

  private void handleLogging()
  {
    Logger rootLogger = Logger.getLogger("");
    Handler handler = null;
    Handler[] h = rootLogger.getHandlers();
    for (int i=0; i<h.length; i++) {
      if (h[i] instanceof ConsoleHandler) {
	handler = h[i];
      }
    }
    if (handler == null) {
      handler = new ConsoleHandler();
      rootLogger.addHandler(handler);
    }
    handler.setLevel(mVerbosity);
    Logger.getLogger("net.sourceforge.czt.gnast").setLevel(mVerbosity);
  }

  public void generate(String name)
  {
    String methodName = "generate";
    
    sLogger.entering(sClassName, methodName, name);
    mApgen.addToContext("class", Apgen.parseMap(mAstProperties, name));
    mApgen.setTemplate((String)mAstProperties.get(name + ".Template"));
    String filename =
      toFileName((String)mAstProperties.get("BasePackage")
		 + "." + 
		 (String)mAstProperties.get(name + ".Package"),
		 (String)mAstProperties.get(name + ".Name"));
    createFile(filename);
    sLogger.exiting(sClassName, methodName);
  }

  /**
   * The main code generator method.
   */
  public void generate(String[] args)
  {
    parseArguments(args);
    handleLogging();

    init();
    GnastProject project = null;
    try {
      project = new SchemaProject(mSchemaFile, mMapping);
    } catch(RuntimeException e) {
      throw e;
    } catch(Exception e) {
      sLogger.severe(e.getMessage());
      e.printStackTrace();
      return;
    }
    Map classes = project.getAstClasses();
    
    String basePackage =
      mAstProperties.getProperty(project.getTargetNamespace());
    sLogger.info("Using package " + basePackage + " for namespace "
		 + project.getTargetNamespace());
    mAstProperties.setProperty("BasePackage", basePackage);

    mApgen = new Apgen(mAstProperties);
    mApgen.addToContext("classes", classes);
    mJavadoc = loadProperties("src/vm/javadoc.properties");
    mApgen.addToContext("javadoc", mJavadoc);
      

    
    // ******************************
    // AstToJaxb, JaxbToAst
    // ******************************
    generate("AstToDomVisitor");
    generate("AstToJaxbVisitor");
    generate("JaxbToAstVisitor");

    generate("AstVisitorInterface");
    generate("AstFactoryInterface");
    generate("AstFactoryImpl");
    
    // ******************************
    // Generate Ast Classes and Interfaces
    // ******************************
    String filename;
    
    generate("HierarchicalAstVisitor");

    Map astClasses = project.getAstClasses();
    for (Iterator iter = astClasses.values().iterator(); iter.hasNext();) {
      GnastClass c = (GnastClass) iter.next();
      mApgen.addToContext("class", c);
      
      sLogger.fine("Generating class file for " + c.getName());
      filename = toFileName("net.sourceforge.czt.core.impl",
			    c.getName() + "Impl");
      mApgen.setTemplate("src/vm/AstClass.vm");
      createFile(filename);

      sLogger.fine("Generating interface file for " + c.getName());
      filename = toFileName("net.sourceforge.czt.core.ast", c.getName());
      mApgen.setTemplate("src/vm/AstInterface.vm");
      createFile(filename);
    }

    Map enumClasses = ((SchemaProject)project).getEnumerations();
    for (Iterator iter = enumClasses.keySet().iterator(); iter.hasNext();) {
      String enumName = (String) iter.next();
      mApgen.addToContext("Name", enumName);
      mApgen.addToContext("Values", enumClasses.get(enumName));

      filename = toFileName("net.sourceforge.czt.core.ast", enumName);
      mApgen.setTemplate("src/vm/Enum.vm");
      createFile(filename);
    }
  }

  /**
   * <p>Applies the context to the template and writes
   * the result to the given file name.</p>
   * <p>Catches all exceptions (except runtime exceptions)
   * and writes logging information.</p>
   *
   * @param  templateName   the name of the template.
   * @param  context        the context to be used when applying the template.
   * @param  fileName       the file name to which to output is written.
   * @return <code>true</code> if the operation was successful;
   *         <code>false</code> otherwise.
   */
  public boolean applyTemplate(String templateName,
			       VelocityContext context,
			       String fileName)
  {
    String methodName = "applyTemplate";
    sLogger.entering(sClassName, methodName);
    boolean success = false;
    try {
      FileWriter writer = new FileWriter(fileName);
      if (applyTemplate(templateName, context, writer))
      {
	sLogger.info("Writing file " + fileName);
	writer.flush();
	writer.close();
	success = true;
      }
    } catch(IOException e) {
      sLogger.severe("Could not open file " + fileName + " for writing.");
      sLogger.severe(e.getMessage());
    }
    sLogger.exiting(sClassName, methodName, new Boolean(success));
    return success;
  }

  /**
   * <p>Applies the context to the template and writes
   * the result to the given file name.</p>
   * <p>Catches all exceptions (except runtime exceptions)
   * and writes logging information.</p>
   *
   * @param  fileName       the file name to which to output is written.
   * @return <code>true</code> if the operation was successful;
   *         <code>false</code> otherwise.
   */
  public boolean createFile(String fileName)
  {
    String methodName = "applyTemplate";
    sLogger.entering(sClassName, methodName);
    boolean success = false;
    try {
      File tempFile = File.createTempFile("gnast", ".vr");
      tempFile.deleteOnExit();
      sLogger.fine("Using temporary file " + tempFile.toString());
      FileWriter writer = new FileWriter(tempFile);
      mApgen.setWriter(writer);
      if (mApgen.generate(Level.SEVERE))
      {
	writer.flush();
	writer.close();
	sLogger.info("Writing file " + fileName);
	File file = new File(fileName);
	new File(file.getParent()).mkdirs();
	writer = new FileWriter(fileName);
	FileReader reader = new FileReader(tempFile);
	int c;
	while((c = reader.read()) != -1) {
	  writer.write(c);
	}
	reader.close();
	writer.close();
	success = true;
      }
    } catch(IOException e) {
      sLogger.severe(e.getMessage());
    }
    
    sLogger.exiting(sClassName, methodName, new Boolean(success));
    return success;
  }

  /**
   * <p>Applies the context to the template and writes
   * the result to the given writer.</p>
   * <p>Catches all exceptions and writes logging information.</p>
   *
   * @param  templateName   the name of the template.
   * @param  context        the context to be used when applying the template.
   * @param  writer         the writer where the output is written into.
   * @return <code>true</code> if the operation was successful;
   *         <code>false</code> otherwise.
   */
  public boolean applyTemplate(String templateName,
			       VelocityContext context,
			       Writer writer)
  {
    String methodName = "applyTemplate";
    sLogger.entering(sClassName, methodName);
    sLogger.fine("Reading template file " + templateName + ".");
    boolean success = false;
    try {
      Template template = Velocity.getTemplate(templateName);
      template.merge(context, writer);
      success = true;
    } catch(NullPointerException e) {
      sLogger.fine("Could not open template " + templateName + ".");
    } catch(ParseErrorException e) {
      throw new GnastException("Parse error in " + templateName + ".", e);
    } catch(ResourceNotFoundException e) {
      sLogger.fine(e.getMessage());
    } catch(Exception e) {
      e.printStackTrace();
    }
    sLogger.exiting(sClassName, methodName, new Boolean(success));
    return success;
  }

  /**
   * <p>Returns a string representing the java file name
   * for the given package and class name.</p>
   * <p>The java file name is the concatenation of the destination
   * directory, the directory name derived by replacing all dots in the
   * package name with the file separator character, and
   * the class name followed by ".java".</p>
   * <p>Note that it is not checked
   * whether the given package and class names are valid.</p>
   *
   * @param packageName    the name of the package.
   * @param className  the name of the class.
   * @return the file name.
   */
  public String toFileName(String packageName, String className)
  {
    return mDestDir
      + File.separatorChar
      + packageName.replace('.', File.separatorChar)
      + File.separatorChar
      + className
      + ".java";
  }

  // ############################################################
  // ##################### STATIC METHODS #######################
  // ############################################################

  /**
   * Returns the properties provided in the given file.
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
  public static Properties loadProperties(String filename)
  {
    final String methodName = "loadProperties";
    sLogger.entering(sClassName, methodName, filename);
    Properties erg = new Properties();
    if (filename != null) {
      try {
	erg.load(new FileInputStream(filename));
      } catch(FileNotFoundException e) {
	sLogger.warning("Cannot find property file " + filename);
      } catch(java.io.IOException e) {
	sLogger.warning("Cannot read property file " + filename);
      }
    }
    return erg;
  }

  /**
   * The main method.
   */
  public static void main (String[] args)
  {
    Gnast gen = new Gnast();
    gen.generate(args);
  }
}
