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
import java.util.*;
import java.util.Properties;
import java.util.logging.Level;

import net.sourceforge.czt.gnast.schema.*;
import net.sourceforge.czt.gnast.gen.*;

/**
 * A project.
 *
 * @author Petra Malik
 * @czt.todo Provide a project which cannot generate its classes
 *           when <code>global</code> is false.
 */
public class Project
  extends Debug
  implements JProject
{
  // ############################################################
  // ##################### MEMBER VARIABLES #####################
  // ############################################################

  private final String mappingFile_ = "mapping.properties";

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
   * <p>The mapping properties.</p>
   */
  private Properties mapping_;

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * Creates a new project from the given schema file.
   *
   * @param filename the name of the schema file.
   * @param global global settings used by all projects.
   * @throws NullPointerException if <code>filename</code> is
   *         <code>null</code>.
   */
  public Project(String filename, GlobalProperties global)
  {
    logFine("Reading schema " + filename);
    if (filename == null) throw new NullPointerException();
    global_ = global;

    mapping_ = Gnast.loadProperties(mappingFile_);
    try {
      project_ = new SchemaProject(filename, mapping_, global_);
    }
    catch (javax.xml.parsers.ParserConfigurationException exception) {
      logSevere("Parse error while parsing " + filename);
      logSevere(exception.getMessage());
    }
    catch (org.xml.sax.SAXException exception) {
      logSevere("Sax error while parsing " + filename);
      logSevere(exception.getMessage());
    }
    catch (java.io.IOException exception) {
      logSevere("IO error while parsing " + filename);
      logSevere(exception.getMessage());
    }
    catch (XSDException exception) {
      logSevere("Error while parsing " + filename);
      logSevere(exception.getMessage());
    }
  }

  // ############################################################
  // ################### (NON-STATC) METHODS ####################
  // ############################################################

  // ******************* CODE GENERATION ************************

  /**
   * Generates the package description for a given package name.
   *
   * @throws NullPointerException if <code>name</code>
   *                              is <code>null</code>.
   */
  protected void generatePackageDescription(String name)
  {
    String methodName = "generate";
    logEntering(methodName, name);

    if (name == null) {
      NullPointerException e = new NullPointerException();
      logExiting(methodName, e);
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

    logExiting(methodName);
  }

  protected void generate(String id)
  {
    String name = project_.getClassName(id);
    String template = project_.getTemplate(id);
    String packageName = project_.getPackage(id);
    String addCodeFilename = "src/vm/"
      + getBasePackage() + "." + packageName + "." + name + ".java";
    File addCodeFile = new File(global_.getBaseDir() + "/" + addCodeFilename);
    if (! addCodeFile.exists()) {
      addCodeFilename = "src/vm/" + name + ".java";
      addCodeFile = new File(global_.getBaseDir() + "/" + addCodeFilename);
    }

    if (name == null || template == null || packageName == null) {
      logSevere("Cannot generate class with id " + id +
                " for project " + getName());
      return;
    }

    Map<String,Object> map = new HashMap<String,Object>();
    map.put("Name", name);
    map.put("Package", packageName);
    if (addCodeFile.exists()) {
      map.put("AdditionalCodeFilename", addCodeFilename);
    }
    apgen_.addToContext("class", map);
    apgen_.setTemplate("src/vm/" + template);
    String filename =
      global_.toFileName(getBasePackage() + "." + packageName,
                         name);
    createFile(filename);
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
    final String methodName = "createFile";
    logEntering(methodName);
    boolean success = false;
    try {
      File tempFile = File.createTempFile("gnast", ".vr");
      tempFile.deleteOnExit();
      logFine("Using temporary file " + tempFile.toString());
      FileWriter writer = new FileWriter(tempFile);
      apgen_.setWriter(writer);
      if (apgen_.generate(Level.SEVERE)) {
        writer.flush();
        writer.close();
        logInfo("Writing file " + fileName);
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
      logSevere(e.getMessage());
    }

    logExiting(methodName, new Boolean(success));
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
    Properties initProps = new Properties();
    initProps.put("velocimacro.library",
                  "src/vm/macros.vm");
    initProps.put("file.resource.loader.path",
                  global_.getBaseDir());
    apgen_ = new Apgen(global_.getDefaultContext(), initProps);
    if (project_.getImportProject() != null) {
      Project blubb = project_.getImportProject();

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

    // ******************************
    // Package Descriptions
    // ******************************
    generatePackageDescription(getAstPackage());
    generatePackageDescription(getImplPackage());
    generatePackageDescription(getVisitorPackage());
    generatePackageDescription(getJaxbPackage());

    // ******************************
    // AstToJaxb, JaxbToAst
    // ******************************
    generate("AstToJaxb");
    generate("JaxbToAst");

    generate("AstVisitor");
    generate("factory");
    generate("factoryImpl");
    generate("convFactory");
    generate("flyFactory");
    generate("createVisitor");

    // ******************************
    // Generate Ast Classes and Interfaces
    // ******************************
    String filename;

    Map astClasses = project_.getAstClasses();
    for (Iterator iter = astClasses.values().iterator(); iter.hasNext();) {
      JAstObject c = (JAstObject) iter.next();
      apgen_.addToContext("class", c);

      logFine("Generating class file for " + c.getName());
      filename = global_.toFileName(c.getImplPackage(),
                                    c.getImplName());
      apgen_.setTemplate("src/vm/AstClass.vm");
      createFile(filename);

      logFine("Generating interface file for " + c.getName());
      filename = global_.toFileName(c.getPackage(),
                                    c.getName());
      apgen_.setTemplate("src/vm/AstInterface.vm");
      createFile(filename);

      logFine("Generating visitor for " + c.getName());
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
    logEntering(methodName, objectId);

    JObject result = null;
    if (objectId != null) {
      if (objectId.equals("Term")) {
        return new JObjectImpl("Term", "net.sourceforge.czt.base.ast");
      }
      if (objectId.equals("TermImpl")) {
        return new JObjectImpl("TermImpl", "net.sourceforge.czt.base.impl");
      }
      String objectName = project_.getClassName(objectId);
      String objectPackage = project_.getPackage(objectId);
      if (objectName != null && objectPackage != null) {
        return new JObjectImpl(objectName,
                               getBasePackage() + "." +
                               objectPackage);
      }
      else if (objectId.endsWith("Impl")) {
        result = new JObjectImpl(objectId, getImplPackage(), this);
      }
      else {
        result = new JObjectImpl(objectId, getAstPackage(), this);
      }
    }
    logExiting(methodName, result);
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
  public List<Project> getImportedProjects()
  {
    String methodName = "getImportedProjects";
    logEntering(methodName);

    List<Project> result = new Vector<Project>();
    Project project = project_.getImportProject();
    if (project != null) {
      result.addAll(project.getImportedProjects());
      result.add(project);
    }
    logExiting(methodName, result);
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
   * and classes generated by JAXB go in.
   *
   * @return the JAXB package name
   *         (should never be <code>null</code>).
   */
  public String getJaxbGenPackage()
  {
    return project_.getJaxbGenPackage();
  }

  /**
   * The name of the package where all the classes for
   * Jaxb support go in.
   *
   * @return the Jaxb package name
   *         (should never be <code>null</code>).
   */
  public String getJaxbPackage()
  {
    return project_.getJaxbPackage();
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

  public String getName()
  {
    return project_.getName();
  }

  public String getTargetNamespace()
  {
    return project_.getTargetNamespace();
  }
}
