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

import java.io.*;
import java.net.URL;
import java.util.*;
import java.util.logging.Level;

import net.sourceforge.czt.gnast.schema.*;
import net.sourceforge.czt.gnast.gen.*;

/**
 * A project.
 *
 * @author Petra Malik
 * @author Andrius Velykis
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

  // ############################################################
  // ####################### CONSTRUCTORS #######################
  // ############################################################

  /**
   * Creates a new project from the given schema file.
   *
   * @param url the location of the schema file.
   * @param global global settings used by all projects.
   * @throws NullPointerException if <code>url</code> is
   *         <code>null</code>.
   */
  public Project(URL url, Properties mapping, GlobalProperties global)
  {
    logFine("Reading schema " + url);
    if (url == null) throw new NullPointerException();
    global_ = global;

    try {
      project_ = new SchemaProject(url, mapping, global_, this);
    }
    catch (javax.xml.parsers.ParserConfigurationException exception) {
      logSevere("Parse error while parsing " + url);
      logSevere(exception.getMessage());
    }
    catch (org.xml.sax.SAXException exception) {
      logSevere("Sax error while parsing " + url);
      logSevere(exception.getMessage());
    }
    catch (java.io.IOException exception) {
      logSevere("IO error while parsing " + url);
      logSevere(exception.getMessage());
    }
    catch (XSDException exception) {
      logSevere("Error while parsing " + url);
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
    String template = StringUtils.capitalize(last) + "Package.vm";
    String filename = global_.toDirectoryName(name) + "package.html";
    createFileIfNeeded(filename, template, Collections.<String>emptySet());

    logExiting(methodName);
  }
  
  protected void generate(String id)
  {
    String name = project_.getClassName(id);
    String template = project_.getTemplate(id);
    String packageName = project_.getPackage(id);
    
    if (name == null || template == null || packageName == null) {
      logSevere("Cannot generate class with id " + id +
                " for project " + getName());
      return;
    }
    
    String javaName = name + ".java";
    String qualifiedJavaName = getBasePackage() + "." + packageName + "." + javaName;
    
    // check fully qualified name
    String addCodeFilename = global_.resolvePath(qualifiedJavaName);
    if (addCodeFilename == null) {
      // check short name
      addCodeFilename = global_.resolvePath(javaName);
    }

    Map<String,Object> map = new HashMap<String,Object>();
    map.put("Name", name);
    map.put("Package", packageName);
    if (addCodeFilename != null) {
      map.put("AdditionalCodeFilename", addCodeFilename);
    }
    apgen_.addToContext("class", map);
    String filename =
      global_.toFileName(getBasePackage() + "." + packageName,
                         name);
    createFileIfNeeded(filename, template, Arrays.asList(javaName, qualifiedJavaName));
  }

  private boolean createFileIfNeeded(String fileName, String templateName, 
      Collection<? extends String> relatedTemplates)
  {
    
    boolean generate = global_.forceGenerateAll(); 
    if (!generate) {
      // check if any of the template files (or the output file) is changed
      Set<String> testFiles = new HashSet<String>();
      testFiles.add(fileName);
      testFiles.add(templateName);
      testFiles.addAll(relatedTemplates);
      generate = containsAny(global_.getChangedFiles(), testFiles);
    }
    
    if (!generate) {
      // nothing's changed - do not create the file
      return false;
    }
    
    apgen_.setTemplate(templateName);
    return createFile(fileName);
  }
  
  private boolean containsAny(Collection<?> col1, Collection<?> col2) {
    
    for (Object e2 : col2) {
      if (col1.contains(e2)) {
        return true;
      }
    }
    
    return false;
  }
  
  private Set<String> getAstFileNames(JAstObject astObj)
  {
    Set<String> astFileNames = new HashSet<String>();
    String code = astObj.getAdditionalCodeFilename();
    if (code != null) {
      astFileNames.add(code);
    }
    
    String impl = astObj.getAdditionalImplCodeFilename();
    if (impl != null) {
      astFileNames.add(impl);
    }

    return astFileNames;
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
    
    File file = new File(fileName);
    Writer writer = null;
    
    // make parent directory structure
    File parent = file.getParentFile();
    if (parent != null) {
      parent.mkdirs();
    }
    
    try {
      writer = new OutputStreamWriter(
          global_.getBuildContext().newFileOutputStream(file));
      
      apgen_.setWriter(writer);
      logInfo("Writing file " + fileName);
      apgen_.generate(Level.SEVERE);
      
      success = true;
    }
    catch (IOException e) {
      logSevere(e.getMessage());
    } finally {
      
      // close the output writer
      if (writer != null) {
        try {
          writer.close();
        }
        catch (IOException e) {
          logSevere(e.getMessage());
        }
      }
      
    }

    logExiting(methodName, new Boolean(success));
    return success;
  }

  /**
   * Concatenates all template paths into one comma-separated string.
   * @return
   */
  private String getTemplatePathURLs() {
    
    List<URL> templatePaths = new ArrayList<URL>();
    
    // add all paths as URLs
    for (URL templateDir : global_.getTemplatePaths()) {
      templatePaths.add(templateDir);
    }
    
    StringBuilder concat = new StringBuilder();
    String sep = "";
    for (URL templatePath : templatePaths) {
      concat.append(sep);
      concat.append(templatePath);
      if (!templatePath.toString().endsWith("/")) {
        // append directory separator at the end, otherwise lookup fails
        concat.append("/");
      }
      sep = ",";
    }
    
    return concat.toString();
  }
  
  public Map<String, ? extends JAstObject> getAstClasses()
  {
  	return Collections.unmodifiableMap(project_.getAstClasses());
  }
  
  public boolean isKnownClass(String type)
  {
  	return getAstClasses().containsKey(type);
  }
  
  public boolean isKnownEnumeration(String type)
  {
	return project_.isKnownEnumeration(type);
  }
  
  public String getFullEnumName(String type, boolean asJaxb)
  {
	return project_.getFullEnumName(type, asJaxb);
  }
  
  /**
   * Generates all classes for this project.
   *
   * @czt.todo Clean up the Exception mess.
   */
  public void generate()
    throws Exception
  {
    Map<?, ?> classes = project_.getAstClasses();
    Properties initProps = new Properties();
    initProps.put("velocimacro.library", "macros.vm");
    /*
     * Use URL resource loader. This way we can indicate template roots both from the JAR files
     * as well as from dependent project files. The templates are loaded either from GnAST JAR
     * or from additional file locations indicated during runtime.
     */
    initProps.put("resource.loader", "url");
    initProps.put("url.resource.loader.root", getTemplatePathURLs());
    initProps.put("url.resource.loader.class", "org.apache.velocity.runtime.resource.loader.URLResourceLoader");
    
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

    Map<String, ? extends JAstObject> astClasses = project_.getAstClasses();
    for (JAstObject c : astClasses.values()) {
      apgen_.addToContext("class", c);
      Set<String> astFileNames = getAstFileNames(c);

      logFine("Generating class file for " + c.getName());
      filename = global_.toFileName(c.getImplPackage(),
                                    c.getImplName());
      createFileIfNeeded(filename, "AstClass.vm", astFileNames);

      logFine("Generating interface file for " + c.getName());
      filename = global_.toFileName(c.getPackage(),
                                    c.getName());
      createFileIfNeeded(filename, "AstInterface.vm", astFileNames);

      logFine("Generating visitor for " + c.getName());
      filename = global_.toFileName(getVisitorPackage(),
                                    c.getName() + "Visitor");
      createFileIfNeeded(filename, "AstVisitorInterface.vm", astFileNames);
    }

    Map<String, List<String>> enumClasses = project_.getEnumerations();
    for (String enumName : enumClasses.keySet()) {
      apgen_.addToContext("Name", enumName);
      apgen_.addToContext("Values", enumClasses.get(enumName));

      filename = global_.toFileName(getAstPackage(),
                                    enumName);
      createFileIfNeeded(filename, "Enum.vm", Collections.<String>emptySet());
    }
  }

  // ****************** INTERFACE JProject ************************

  public JAstObject getAstObject(String objectName)
  {
    Map<String, ? extends JAstObject> mapping = project_.getAstClasses();
    return mapping.get(objectName);
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
  @Override
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
  @Override
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
  @Override
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
