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
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

import net.sourceforge.czt.gnast.schema.*;

/**
 * A project.
 *
 * @author Petra Malik
 */
public class Project implements ProjectProperties
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  /**
   * The class name of this class; used for logging purposes.
   */
  private static final String sClassName = "Project";

  /**
   * The logger used when logging information is provided.
   */
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.gnast" + "." + sClassName);

  /**
   * The project properties as provided by the properties file.
   *
   * @czt.todo This member variable should removed.
   */
  private Properties mProperties = new Properties();

  /**
   * <p>The global properties for this code generation attempt.</p>
   */
  private GlobalProperties mGlobal;

  /**
   * <p>The generator used for generating the files.</p>
   */
  private Apgen mApgen;

  /**
   * <p>The schema file name.</p>
   */
  private String mSchemaFileName;

  /**
   * <p>The mapping properties.</p>
   */
  private Properties mMapping;

  /**
   * <p>The base package.
   * All the generated interfaces and classes are
   * in subpackages of this package.</p>
   */
  private String mPackage;

  /**
   * <p>The javadoc documentation for this project.</p>
   */
  private Properties mJavadoc = new Properties();

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * @param name the name of the project.
   * @param global global settings used by all projects.
   * @throws ConfigurationException if a required property cannot be read.
   * @throws NullPointerException if one of the arguments is <code>null</code>.
   */
  public Project(String name, GlobalProperties global)
    throws ConfigurationException
  {
    sLogger.fine("Creating project " + name);
    if (name == null || global == null) throw new NullPointerException();
    mGlobal = global;

    String filename = name + ".properties";
    try {
      sLogger.config("Loading properties file " + filename);
      mProperties.load(new FileInputStream(filename));
      mSchemaFileName = getRequiredProperty("schema.file");
      mMapping = Gnast.loadProperties(getRequiredProperty("mapping.file"));
      mJavadoc = Gnast.loadProperties("src/vm/javadoc.properties");
    } catch(FileNotFoundException e) {
      throw
	new ConfigurationException("Cannot find property file " + filename);
    } catch(java.io.IOException e) {
      throw
	new ConfigurationException("Cannot read property file " + filename);
    }
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ******************** INITIALISING **************************

  /**
   * @param name the name of the property.
   * @throws ConfigurationException if the property cannot be read.
   */
  private String getRequiredProperty(String name)
    throws ConfigurationException
  {
    String result = mProperties.getProperty(name);
    if (result == null) {
      throw new ConfigurationException();
    }
    return result;
  }

  // ****************** CODE GENERATION ************************

  /**
   *
   * @throws NullPointerException if <code>name</code> is <code>null</code>.
   */
  protected void generate(String name)
  {
    String methodName = "generate";
    sLogger.entering(sClassName, methodName, name);

    if (name == null) {
      NullPointerException e = new NullPointerException();
      sLogger.exiting(sClassName, methodName, e);
      throw e;
    }

    mApgen.addToContext("class", Apgen.parseMap(mProperties, name));
    mApgen.setTemplate((String)mProperties.get(name + ".Template"));
    String filename =
      mGlobal.toFileName((String)mProperties.get("BasePackage")
			 + "." + 
			 (String)mProperties.get(name + ".Package"),
			 (String)mProperties.get(name + ".Name"));
    createFile(filename);

    sLogger.exiting(sClassName, methodName);
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
  protected boolean createFile(String fileName)
  {
    String methodName = "createFile";
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
   * @czt.todo Clean up the Exception mess.
   */
  public void generate()
    throws Exception
  {
    GnastProject project =
      new SchemaProject(mSchemaFileName,
			mMapping,
			this,
			mProperties);
    Map classes = project.getAstClasses();
    
    mApgen = new Apgen(mGlobal.getDefaultContext());
    for (Enumeration e = mProperties.propertyNames(); e.hasMoreElements();) {
      String propertyName = (String) e.nextElement();
      mApgen.addToContext(propertyName.replace('.', '_'),
			  mProperties.getProperty(propertyName));
    }
    mApgen.addToContext("classes", classes);
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
      filename = mGlobal.toFileName((String)mProperties.get("BasePackage") +
				    "." +
				    (String)mProperties.get("ImplPackage"),
				    c.getName() + "Impl");
      mApgen.setTemplate("src/vm/AstClass.vm");
      createFile(filename);

      sLogger.fine("Generating interface file for " + c.getName());
      filename = mGlobal.toFileName((String)mProperties.get("BasePackage") +
				    "." +
				    (String)mProperties.get("AstPackage"),
				    c.getName());
      mApgen.setTemplate("src/vm/AstInterface.vm");
      createFile(filename);
    }

    Map enumClasses = ((SchemaProject)project).getEnumerations();
    for (Iterator iter = enumClasses.keySet().iterator(); iter.hasNext();) {
      String enumName = (String) iter.next();
      mApgen.addToContext("Name", enumName);
      mApgen.addToContext("Values", enumClasses.get(enumName));

      filename = mGlobal.toFileName((String)mProperties.get("BasePackage") +
				    "." +
				    (String)mProperties.get("AstPackage"),
				    enumName);
      mApgen.setTemplate("src/vm/Enum.vm");
      createFile(filename);
    }
  }

  // ****************** INTERFACE ProjectProperties ************************

  /**
   * The name of the package where all the AST interfaces go in.
   *
   * @return the AST interface package name.
   */
  public String getAstPackage()
  {
    return mProperties.getProperty("BasePackage") + "."
      + mProperties.getProperty("AstPackage");
  }

  /**
   * The name of the package where all the AST
   * implementation classes go in.
   *
   * @return the AST (implementation) class package name.
   */
  public String getImplPackage()
  {
    return mProperties.getProperty("BasePackage") + "."
      + mProperties.getProperty("ImplPackage");
  }
}
