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
import net.sourceforge.czt.gnast.gen.*;

/**
 * A project.
 *
 * @author Petra Malik
 * @czt.todo Provide a project which cannot generate its classes
 *           when <code>global</code> is false.
 */
public class Project implements JProject
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  /**
   * The class name of this class; used for logging purposes.
   */
  private static final String CLASS_NAME = "Project";

  /**
   * The logger used when logging messages are written.
   */
  private static final Logger LOGGER =
    Logger.getLogger("net.sourceforge.czt.gnast" + "." + CLASS_NAME);

  /**
   * The project properties as provided by the properties file.
   *
   * @czt.todo This member variable should be removed.
   */
  private Properties properties_ = new Properties();

  /**
   * The schema project.
   */
  private SchemaProject project_;

  /**
   * <p>The global properties for this code generation attempt.</p>
   */
  private GlobalProperties global_;

  /**
   * <p>The generator used for generating the files.</p>
   */
  private Apgen apgen_;

  /**
   * <p>The schema file name.</p>
   */
  private String schemaFilename_;

  /**
   * <p>The mapping properties.</p>
   */
  private Properties mapping_;

  /**
   * <p>The base package.
   * All the generated interfaces and classes are
   * in subpackages of this package.</p>
   */
  private String packageName_;

  /**
   * <p>The javadoc documentation for this project.</p>
   */
  private Properties javadoc_ = new Properties();

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * @param name the name of the project.
   * @param global global settings used by all projects.
   * @throws ConfigurationException if a required property cannot be read.
   * @throws NullPointerException if <code>name</code> is <code>null</code>.
   * @czt.todo Clean up the Exception mess.
   */
  public Project(String name, GlobalProperties global)
    throws Exception
  {
    LOGGER.fine("Creating project " + name);
    if (name == null) throw new NullPointerException();
    global_ = global;

    String filename = name + ".properties";
    try {
      LOGGER.config("Loading properties file " + filename);
      properties_.load(new FileInputStream(filename));
      schemaFilename_ = getRequiredProperty("schema.file");
      mapping_ = Gnast.loadProperties(getRequiredProperty("mapping.file"));
      packageName_ = getRequiredProperty("BasePackage");
      javadoc_ = Gnast.loadProperties("src/vm/javadoc.properties");
      project_ = new SchemaProject(schemaFilename_,
                                   mapping_,
                                   global_);
    }
    catch (FileNotFoundException e) {
      throw
        new ConfigurationException("Cannot find property file " + filename);
    }
    catch (IOException e) {
      throw
        new ConfigurationException("Cannot read property file " + filename);
    }
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ******************** INITIALISING **************************

  /**
   * Returns the value of the given property if it is present;
   * or throws an exception if the property cannot be found.
   *
   * @param name the name of the property.
   * @throws ConfigurationException if the property cannot be read.
   */
  private String getRequiredProperty(String name)
    throws ConfigurationException
  {
    String result = properties_.getProperty(name);
    if (result == null) {
      throw new ConfigurationException("Cannot find property " + name);
    }
    return result;
  }

  // ****************** CODE GENERATION ************************

  /**
   * Generates the package description for a given package name.
   *
   * @throws NullPointerException if <code>name</code>
   *                              is <code>null</code>.
   */
  protected void generatePackageDescription(String name)
  {
    String methodName = "generate";
    LOGGER.entering(CLASS_NAME, methodName, name);

    if (name == null) {
      NullPointerException e = new NullPointerException();
      LOGGER.exiting(CLASS_NAME, methodName, e);
      throw e;
    }
    String[] splitted = name.replace('.', ':').split(":");
    String last = name;
    if (splitted.length > 0) {
      last = splitted[splitted.length - 1];
    }
    apgen_.setTemplate("src/vm/"
                       + StringUtils.capitalize(last)
                       + "Package.vm");
    String filename =
      global_.toDirectoryName(name) + "package.html";
    createFile(filename);

    LOGGER.exiting(CLASS_NAME, methodName);
  }

  /**
   * Generates the given class.
   *
   * @throws NullPointerException if <code>name</code> is <code>null</code>.
   */
  protected void generate(String name)
  {
    String methodName = "generate";
    LOGGER.entering(CLASS_NAME, methodName, name);

    if (name == null) {
      NullPointerException e = new NullPointerException();
      LOGGER.exiting(CLASS_NAME, methodName, e);
      throw e;
    }

    apgen_.addToContext("class", Apgen.parseMap(properties_, name));
    apgen_.setTemplate((String) properties_.get(name + ".Template"));
    String filename =
      global_.toFileName(getBasePackage()
                         + "."
                         + (String) properties_.get(name + ".Package"),
                         (String) properties_.get(name + ".Name"));
    createFile(filename);

    LOGGER.exiting(CLASS_NAME, methodName);
  }

  protected void generateFactory()
  {
    String name = project_.getFactoryClassName();
    String template = project_.getFactoryTemplate();
    String packageName = project_.getFactoryPackage();

    Map map = new HashMap();
    map.put("Name", name);
    map.put("Package", packageName);
    apgen_.addToContext("class", map);
    apgen_.setTemplate("src/vm/" + template);
    String filename =
      global_.toFileName(getBasePackage() + "." + packageName,
                         name);
    createFile(filename);
  }

  protected void generateFactoryImpl()
  {
    String name = project_.getFactoryImplClassName();
    String template = project_.getFactoryImplTemplate();
    String packageName = project_.getFactoryImplPackage();

    Map map = new HashMap();
    map.put("Name", name);
    map.put("Package", packageName);
    apgen_.addToContext("class", map);
    apgen_.setTemplate("src/vm/" + template);
    String filename =
      global_.toFileName(getBasePackage() + "." + packageName,
                         name);
    createFile(filename);
  }

  public void getFactoryName()
  {
    
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
    LOGGER.entering(CLASS_NAME, methodName);
    boolean success = false;
    try {
      File tempFile = File.createTempFile("gnast", ".vr");
      tempFile.deleteOnExit();
      LOGGER.fine("Using temporary file " + tempFile.toString());
      FileWriter writer = new FileWriter(tempFile);
      apgen_.setWriter(writer);
      if (apgen_.generate(Level.SEVERE)) {
        writer.flush();
        writer.close();
        LOGGER.info("Writing file " + fileName);
        File file = new File(fileName);
        new File(file.getParent()).mkdirs();
        writer = new FileWriter(fileName);
        FileReader reader = new FileReader(tempFile);
        int c;
        while ((c = reader.read()) != -1) {
          writer.write(c);
        }
        reader.close();
        writer.close();
        success = true;
      }
    }
    catch (IOException e) {
      LOGGER.severe(e.getMessage());
    }

    LOGGER.exiting(CLASS_NAME, methodName, new Boolean(success));
    return success;
  }

  /**
   * Generates all classes for this project.
   *
   * @czt.todo Clean up the Exception mess.
   */
  public void generate()
    throws Exception
  {
    Map classes = project_.getAstClasses();

    apgen_ = new Apgen(global_.getDefaultContext());
    for (Enumeration e = properties_.propertyNames(); e.hasMoreElements();) {
      String propertyName = (String) e.nextElement();
      apgen_.addToContext(propertyName.replace('.', '_'),
                          properties_.getProperty(propertyName));
    }
    if (project_.getImportProject() != null) {
      String projectName = project_.getImportProject();
      Project blubb = new Project(projectName, global_);

      // should be removed in the future
      apgen_.addToContext("ImportPackage", getBasePackage());
      // use this instead:
      apgen_.addToContext("ImportProject", blubb);
    }
    apgen_.addToContext("project", this);
    apgen_.addToContext("projects", getImportedProjects());
    if (getImportedProjects().isEmpty()) {
      apgen_.addToContext("core", this);
    }
    else {
      apgen_.addToContext("core", getImportedProjects().get(0));
    }
    apgen_.addToContext("classes", classes);
    apgen_.addToContext("javadoc", javadoc_);

    // ******************************
    // Package Descriptions
    // ******************************
    generatePackageDescription(getAstPackage());
    generatePackageDescription(getImplPackage());
    generatePackageDescription(getVisitorPackage());
    generatePackageDescription(getDomPackage());
    // TODO: implement the following hack properly
    generatePackageDescription(getBasePackage() + ".jaxb");

    // ******************************
    // AstToJaxb, JaxbToAst
    // ******************************
    generate("AstToDomVisitor");
    generate("AstToJaxbVisitor");
    generate("JaxbToAstVisitor");

    generate("AstVisitorInterface");
    generateFactory();
    generateFactoryImpl();

    // ******************************
    // Generate Ast Classes and Interfaces
    // ******************************
    String filename;

    Map astClasses = project_.getAstClasses();
    for (Iterator iter = astClasses.values().iterator(); iter.hasNext();) {
      JAstObject c = (JAstObject) iter.next();
      apgen_.addToContext("class", c);

      LOGGER.fine("Generating class file for " + c.getName());
      filename = global_.toFileName(c.getImplPackage(),
                                    c.getImplName());
      apgen_.setTemplate("src/vm/AstClass.vm");
      createFile(filename);

      LOGGER.fine("Generating interface file for " + c.getName());
      filename = global_.toFileName(c.getPackage(),
                                    c.getName());
      apgen_.setTemplate("src/vm/AstInterface.vm");
      createFile(filename);

      LOGGER.fine("Generating visitor for " + c.getName());
      filename = global_.toFileName(getVisitorPackage(),
                                    c.getName() + "Visitor");
      apgen_.setTemplate("src/vm/AstVisitorInterface.vm");
      createFile(filename);
    }

    Map enumClasses = project_.getEnumerations();
    for (Iterator iter = enumClasses.keySet().iterator(); iter.hasNext();) {
      String enumName = (String) iter.next();
      apgen_.addToContext("Name", enumName);
      apgen_.addToContext("Values", enumClasses.get(enumName));

      filename = global_.toFileName(getAstPackage(),
                                    enumName);
      apgen_.setTemplate("src/vm/Enum.vm");
      createFile(filename);
    }
  }

  // ****************** INTERFACE JProject ************************

  public JAstObject getAstObject(String objectName)
  {
    Map mapping = project_.getAstClasses();
    return (JAstObject) mapping.get(objectName);
  }

  public JObject getObject(String objectId)
  {
    String methodName = "getObject";
    LOGGER.entering(CLASS_NAME, methodName, objectId);

    JObject result = null;
    if (objectId != null) {
      if (objectId.equals("Term")) {
        return new JObjectImpl("Term", "net.sourceforge.czt.base.ast");
      }
      if (objectId.equals("TermImpl")) {
        return new JObjectImpl("TermImpl", "net.sourceforge.czt.base.impl");
      }
      if (objectId.equals("TermA")) {
        return new JObjectImpl("TermA", "net.sourceforge.czt.base.ast");
      }
      if (objectId.equals("TermAImpl")) {
        return new JObjectImpl("TermAImpl", "net.sourceforge.czt.base.impl");
      }
      if (objectId.equals("factory")) {
        return new JObjectImpl(project_.getFactoryClassName(),
                               project_.getBasePackage() + "." +
                               project_.getFactoryPackage());
      }
      if (objectId.equals("factoryImpl")) {
        return new JObjectImpl(project_.getFactoryImplClassName(),
                               project_.getBasePackage() + "." +
                               project_.getFactoryImplPackage());
      }
      String objectName = properties_.getProperty(objectId + ".Name");
      String objectPackage = properties_.getProperty(objectId + ".Package");
      if (objectName != null && objectPackage != null) {
        result = new JObjectImpl(objectName,
                                 packageName_ + "." + objectPackage,
                                 this);
      }
      else if (objectId.endsWith("Impl")) {
        result = new JObjectImpl(objectId, getImplPackage(), this);
      }
      else {
        result = new JObjectImpl(objectId, getAstPackage(), this);
      }
    }
    LOGGER.exiting(CLASS_NAME, methodName, result);
    return result;
  }

  /**
   * <p>Returns a list of all imported projects
   * starting with the root ancestor project.</p>
   *
   * <p>Each project can import at most one other project.
   * The imported project may import another project.
   * A project that does not import another project is
   * called a root project.</p>
   *
   * @czt.todo Is this method needed at all?
   */
  public List getImportedProjects()
  {
    String methodName = "getImportedProjects";
    LOGGER.entering(CLASS_NAME, methodName);

    List result = new Vector();
    String importedProject = project_.getImportProject();
    if (importedProject != null) {
      Project project = global_.getProject(importedProject);
      if (project != null) {
        result.addAll(project.getImportedProjects());
        result.add(project);
      }
    }
    LOGGER.exiting(CLASS_NAME, methodName, result);
    return result;
  }

  public String getBasePackage()
  {
    return project_.getBasePackage();
  }

  /**
   * The name of the package where all the AST interfaces go in.
   *
   * @return the AST interface package name
   *         (should never be <code>null</code>).
   */
  public String getAstPackage()
  {
    return project_.getAstPackage();
  }

  /**
   * The name of the package where all the AST
   * implementation classes go in.
   *
   * @return the AST (implementation) class package name
   *         (should never be <code>null</code>).
   */
  public String getImplPackage()
  {
    return project_.getImplPackage();
  }

  /**
   * The name of the package where all the JAXB interfaces
   * generated by JAXB go in.
   *
   * @return the JAXB package name
   *         (should never be <code>null</code>).
   * @czt.todo use JaxbGenPackage instead?
   */
  public String getJaxbPackage()
  {
    return getBasePackage()
      + "."
      + properties_.getProperty("JaxbPackage");
  }

  /**
   * The name of the package where all the classes for
   * DOM support go in.
   *
   * @return the DOM package name
   *         (should never be <code>null</code>).
   */
  public String getDomPackage()
  {
    return project_.getDomPackage();
  }

  /**
   * The name of the package where all the AST visitor interfaces go in.
   *
   * @return the AST visitor package name
   *         (should never be <code>null</code>).
   */
  public String getVisitorPackage()
  {
    return project_.getVisitorPackage();
  }

  /**
   * @return the AST package description (can be <code>null</code>).
   */
  public String getAstJavadoc()
  {
    return project_.getPackageDocumentation("ast");
  }

  public JObject getGenObject(String id)
  {
    return project_.getGenObject(id);
  }
}
