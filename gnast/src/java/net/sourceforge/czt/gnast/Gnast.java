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
 * The Gnast command line user interface.
 * This class contains the main method for calling the
 * AST code generator.
 *
 * @author Petra Malik
 */
public class Gnast
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  private static final String sClassName = "Gnast";
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast" + "." + sClassName);

  /**
   * Contains the Gnast properties.
   *
   * @see #init()
   */
  protected Properties mProperties = new Properties();

  protected Properties mJavadoc = new Properties();

  /**
   * The verbosity used for logging purposes.
   */
  private Level mVerbosity = Level.SEVERE;

  private String mSchemaFile = null;

  /**
   * The destination directory where all the generated files go in.
   */
  private String mDestDir = null;

  private Apgen mApgen;

  // ############################################################
  // ######################### METHODS ##########################
  // ############################################################

  /**
   * The main method.
   */
  public static void main (String[] args)
    throws Exception
  {
    Gnast gen = new Gnast();
    gen.generate(args);
  }

  /**
   * Parses the arguments from the command line.
   *
   * @return <code>true</code> if parsing was successful;
   *         <code>false</code> otherwise.
   */
  private boolean parseArguments(String[] args)
  {
    String usage = "class options:\n";
    usage += "  -d, --dest <dir> Generated files go into this directory\n";
    usage += "  -v, --verbose    Verbose; display verbose debugging messages\n";

    int i = 0;

    while (i < args.length && args[i].startsWith("-")) {
      String arg = args[i++];
      if (arg.equals("-verbose") ||
	  arg.equals("--verbose") ||
	  arg.equals("-v"))
      {
	mVerbosity = Level.INFO;
      }
      else if (arg.equals("-vv"))
      {
	mVerbosity = Level.FINE;
      }
      else if (arg.equals("-vvv"))
      {
	mVerbosity = Level.FINER;
      }
      else if (arg.equals("-dest") ||
	       arg.equals("--dest") ||
	       arg.equals("-d"))
      {
	if (i < args.length)
	  mDestDir = args[i++];
	else {
	  System.err.println(arg + " requires a directory name");
	  System.err.println(usage);
	  return false;
	}
      }
    }
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
    mApgen.addToContext("class", Apgen.parseMap(mProperties, name));
    mApgen.setTemplate((String)mProperties.get(name + ".Template"));
    String filename =
      toFileName((String)mProperties.get("BasePackage")
		 + "." + 
		 (String)mProperties.get(name + ".Package"),
		 (String)mProperties.get(name + ".Name"));
    createFile(filename);
    sLogger.exiting(sClassName, methodName);
  }

  /**
   * The main code generator method.
   */
  public void generate(String[] args)
    throws Exception
  {
    parseArguments(args);
    handleLogging();

    init();
    GnastProject project = null;
    if (mSchemaFile != null)
      project = new SchemaProject(mSchemaFile,
				  mProperties.getProperty("mapping.file"));
    Collection classes = project.getAstClasses();
    
    mApgen = new Apgen(mProperties);
    mApgen.addToContext("classes", classes);
    mApgen.addToContext("javadoc", mJavadoc);
    
    // ******************************
    // Using Velocity
    Velocity.init("velocity.properties");
    VelocityContext context = new VelocityContext();
    
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

    Collection astClasses = project.getAstClasses();
    for (Iterator iter = astClasses.iterator(); iter.hasNext();) {
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
   * @param  templateName   the name of the template.
   * @param  context        the context to be used when applying the template.
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
   * @param package    the name of the package.
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

  public void init()
  {
    try {
      mProperties.load(new FileInputStream("gnast.properties"));
    } catch(FileNotFoundException e) {
      sLogger.severe("Cannot find file gnast.properties.");
    } catch(java.io.IOException e) {
      sLogger.severe("Cannot read file gnast.properties.");
    }
    if (mSchemaFile == null) {
      mSchemaFile = mProperties.getProperty("schema.file");
    }
    if (mDestDir == null) {
      mDestDir = mProperties.getProperty("dest.dir");
    }

    try {
      mJavadoc.load(new FileInputStream("src/vm/javadoc.properties"));
    } catch(FileNotFoundException e) {
      sLogger.severe("Cannot find file src/vm/javadoc.properties.");
    } catch(java.io.IOException e) {
      sLogger.severe("Cannot read file src/vm/javadoc.properties.");
    }
  }
}
