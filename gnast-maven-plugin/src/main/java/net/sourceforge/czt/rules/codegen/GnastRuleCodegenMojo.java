/*
  Copyright 2005, 2006, 2007, 2012  Petra Malik, Andrius Velykis
  
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

package net.sourceforge.czt.rules.codegen;

import java.io.File;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Properties;
import java.util.Set;

import net.sourceforge.czt.gnast.ResourceUtils;

import org.sonatype.plexus.build.incremental.BuildContext;
import org.sonatype.plexus.build.incremental.DefaultBuildContext;
import org.w3c.dom.DOMConfiguration;
import org.w3c.dom.DOMError;
import org.w3c.dom.DOMErrorHandler;
import org.w3c.dom.bootstrap.DOMImplementationRegistry;

import org.apache.velocity.runtime.RuntimeInstance;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.Template;

import org.apache.xerces.xs.*;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;
import org.codehaus.plexus.resource.DefaultResourceManager;
import org.codehaus.plexus.resource.PlexusResource;
import org.codehaus.plexus.resource.ResourceManager;
import org.codehaus.plexus.resource.loader.ResourceNotFoundException;


/**
 * @goal rulecodegen
 *
 * @author Petra Malik
 * @author Andrius Velykis
 */
public class GnastRuleCodegenMojo
  extends AbstractMojo 
{

  /**
   * @parameter expression="${project.build.directory}/generated-sources/gnast"
   */
  private File outputDirectory;

  /**
   * @parameter expression="${project.basedir}/src/main/resources/vm/gnast/"
   * @required
   */
  private String templateDirectory;
  
  /**
   * @parameter
   * @required
   */
  private String sourceSchemaLocation;
  
  /**
   * @parameter
   */
  private String packageName = "";

  /**
   * @parameter expression="${project}"
   * @required
   */
  private MavenProject project;
  
  
  /** 
   * Injected by Maven
   * @component
   */
  private BuildContext buildContext;
  
  /**
   * Injected by Maven
   * @component
   */
  private ResourceManager locator;
  
  private Set<String> changedFiles = Collections.emptySet();
  private boolean generateAll = true;
  
  public void execute()
    throws MojoExecutionException
  {
    if (project != null )
    {
      project.addCompileSourceRoot(outputDirectory.getPath());
    }
    
    if (buildContext == null) {
      // non-incremental context by default
      buildContext = new DefaultBuildContext();
    }
    
    URL sourceSchemaUrl = locateResource(sourceSchemaLocation);
    if (sourceSchemaUrl == null) {
      throw new MojoExecutionException("XML schema location cannot be resolved: " + sourceSchemaLocation);
    }
    
    // if the schema has changed, or output directory does not exist, generate all
    this.generateAll = !ResourceUtils.getURLChanges(buildContext, sourceSchemaUrl, false).isEmpty()
        || !outputDirectory.exists();
    this.changedFiles = Collections.emptySet();
    
    URL templateDirectoryUrl = locateResource(templateDirectory);
    if (templateDirectoryUrl == null) {
      throw new MojoExecutionException("Template directory location cannot be resolved: " + templateDirectory);
    }
    
    if (!generateAll) {
      this.changedFiles = ResourceUtils.getURLChanges(buildContext, templateDirectoryUrl, true);
      if (changedFiles.isEmpty()) {
        // nothing has changed - do not need to regenerate the code
        getLog().info( "No changes in source files - code is not regenerated." );
        return;
      }
    }
    
    // replace all dots with dir separators
    String packageDir = packageName.replace(".", "/");
    
    try {
      System.setProperty(DOMImplementationRegistry.PROPERTY,
        "org.apache.xerces.dom.DOMXSImplementationSourceImpl");
      DOMImplementationRegistry registry =
        DOMImplementationRegistry.newInstance();
      XSImplementation impl =
        (XSImplementation) registry.getDOMImplementation("XS-Loader");
      XSLoader schemaLoader = impl.createXSLoader(null);
      DOMConfiguration config = schemaLoader.getConfig();
      DOMErrorHandler errorHandler = new ErrorHandler();
      config.setParameter("error-handler", errorHandler);
      config.setParameter("validate", Boolean.TRUE);
      XSModel model = schemaLoader.loadURI(sourceSchemaUrl.toURI().toString());

      RuntimeInstance velocity = new RuntimeInstance();
      Properties initProps = new Properties();
      
      /*
       * Use URL resource loader. This way we can indicate template roots both from the JAR files
       * as well as from dependent project files.
       */
      initProps.put("resource.loader", "url");
      initProps.put("url.resource.loader.root", templateDirectoryUrl.toString() + "/");
      initProps.put("url.resource.loader.class", "org.apache.velocity.runtime.resource.loader.URLResourceLoader");
      
      velocity.init(initProps);
    
      XSNamedMap map = model.getComponents(XSTypeDefinition.COMPLEX_TYPE);
      List<JokerClass> jokers = new ArrayList<JokerClass>();
      for (int i = 0; i < map.getLength(); i++) {
        XSComplexTypeDefinition item = (XSComplexTypeDefinition) map.item(i);
        String name = item.getName();
        if (name.startsWith("Joker") && ! name.endsWith("Binding") &&
            ! name.equals("Jokers")) {
          final JokerClass jokerClass = new JokerClass(item);
          jokers.add(jokerClass);
          VelocityContext context = new VelocityContext();
          context.put("joker", jokerClass);
          context.put("complex_type", item);
          context.put("isList", name.endsWith("List"));
          String dest = outputDirectory + "/" + packageDir + "/" + "Prover" + name + ".java";
          write(velocity, dest, "Joker.vm", context);
          dest = outputDirectory + "/" + packageDir + "/" + "Prover" + name + "Binding.java";
          write(velocity, dest, "Binding.vm", context);
        }
      }
      final String dest =
        outputDirectory + "/" + packageDir + "/" + "ProverFactory.java";
      VelocityContext context = new VelocityContext();
      context.put("jokers", jokers);
      write(velocity, dest, "Factory.vm", context);
    }
    catch (Exception e) {
      e.printStackTrace();
      throw new MojoExecutionException(e.getMessage(), e);
    }
  }

  private void write(RuntimeInstance velocity,
                            String destination,
                            String templateName,
                            VelocityContext context)
    throws Exception
  {
    
    // check if file sources have changed (or the file itself)
    boolean generate = generateAll || changedFiles.contains(destination) || changedFiles.contains(templateName);
    if (!generate) {
      // this file does not need to be generated
      return;
    }
    
    File dest = new File(destination);
    dest.getParentFile().mkdirs();
    
    Writer writer = new OutputStreamWriter(buildContext.newFileOutputStream(dest));
    Template template = velocity.getTemplate(templateName);
    template.merge(context, writer);
    writer.close();
  }
  
  private URL locateResource(String resourceLocation) throws MojoExecutionException {
    
    if (resourceLocation == null) {
      return null;
    }
    
    if (locator == null) {
      locator = new DefaultResourceManager();
    }
    
    try {
      PlexusResource resource = locator.getResource(resourceLocation);
      return resource.getURL();
    }
    catch (ResourceNotFoundException e) {
      throw new MojoExecutionException("Cannot find resource " + resourceLocation, e);
    }
    catch (IOException e) {
      throw new MojoExecutionException("Cannot find resource URL " + resourceLocation, e);
    }
    
  }
  
}

class ErrorHandler
  implements DOMErrorHandler
{
  public boolean handleError(DOMError error)
  {
    short severity = error.getSeverity();
    if (severity == DOMError.SEVERITY_ERROR) {
      System.err.println("[xs-error]: "+error.getMessage());
    }
    if (severity == DOMError.SEVERITY_WARNING) {
      System.err.println("[xs-warning]: "+error.getMessage());
    }
    return true;
  }
}
