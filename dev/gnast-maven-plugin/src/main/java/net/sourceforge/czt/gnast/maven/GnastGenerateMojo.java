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

package net.sourceforge.czt.gnast.maven;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

import net.sourceforge.czt.gnast.Gnast;
import net.sourceforge.czt.gnast.Gnast.GnastBuilder;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.Component;
import org.apache.maven.plugins.annotations.LifecyclePhase;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.Parameter;
import org.apache.maven.project.MavenProject;
import org.codehaus.plexus.resource.DefaultResourceManager;
import org.codehaus.plexus.resource.PlexusResource;
import org.codehaus.plexus.resource.ResourceManager;
import org.codehaus.plexus.resource.loader.ResourceNotFoundException;
import org.sonatype.plexus.build.incremental.BuildContext;

/**
 * Goal which generates AST classes from XML Schema files using GnAST.
 * <p>
 * The source XML Schema files can be provided by indicating a source directory or explicitly
 * listing the paths.
 * </p>
 * <p>
 * The template and schema paths can be indicated as filesystem paths, URLs, or classpath
 * resources. Refer to Plexus {@link ResourceManager} for more details.
 * </p>
 *
 * @see net.sourceforge.czt.gnast.Gnast
 * @see org.codehaus.plexus.resource.ResourceManager
 * @author Petra Malik
 * @author Andrius Velykis
 */
@Mojo(name = "generate", threadSafe = false, 
      defaultPhase = LifecyclePhase.GENERATE_SOURCES)
public class GnastGenerateMojo
  extends AbstractMojo 
{
  /**
   * The directory where GnAST should generate AST files.
   */
  @Parameter( property = "gnast.outputDirectory", 
              defaultValue = "${project.build.directory}/generated-sources/gnast" )
  private File outputDirectory;

  /**
   * The list of Velocity template directory paths.
   * <p>
   * The files in template paths can be used in GnAST Velocity templates to drive AST generation.
   * </p>
   * <p>
   * Potential values are filesystem paths, URLs, or classpath resources.
   * This parameter is resolved as resource, URL, then file.
   * </p>
   * @see org.codehaus.plexus.resource.ResourceManager
   */
  @Parameter( alias = "templateDirectory", required = true )
  private List<String> templates = new ArrayList<String>();
  
  /**
   * The file defining mappings between XML Schema types and Java types. Follows Java Properties
   * file format, e.g. {@code anyURI = String}.
   */
  @Parameter( property = "gnast.mappingFileLocation", defaultValue = "mapping.properties" )
  private String mappingFileLocation;
  
  /**
   * Add AST finalisers to count finalised AST objects (e.g. for metrics)
   */
  @Parameter( property = "gnast.addAstFinaliser" )
  private Boolean addAstFinaliser;
  
  /**
   * Sets whether the plugin runs in verbose mode.
   */
  @Parameter( property = "gnast.verbose", defaultValue = "false" )
  private boolean verbose;
  
  /**
   * The directory where all XML schema source files are located.
   * <p>
   * At least one of {@link #sourceDirectory} or {@link #sourceSchemas} must
   * be set to find the schemas.
   * </p>
   */
  @Parameter( property = "gnast.sourceDirectory" )
  private File sourceDirectory;
  
  /**
   * An explicit list of XML schema source files to use in generation.
   * <p>
   * Potential values are a filesystem path, a URL, or a classpath resource.
   * This parameter is resolved as resource, URL, then file.
   * </p>
   * <p>
   * At least one of {@link #sourceDirectory} or {@link #sourceSchemas} must
   * be set to find the schemas.
   * </p>
   */
  @Parameter( alias = "schemaLocation" )
  private List<String> sourceSchemas = new ArrayList<String>();
  
  /**
   * The namespace (as indicated in XML Schema file) to generate AST files for.
   */
  @Parameter( property = "gnast.targetNamespace", required = true )
  private String targetNamespace;


  /**
   * The Maven project (used to add generated sources for compilation).
   */
  @Component
  private MavenProject project;
  
  /**
   * The build context, for incremental build support.
   */
  @Component
  private BuildContext buildContext;
  
  /**
   * The resource locator for finding classpath or URL resources.
   */
  @Component
  private ResourceManager locator;
  

  /**
   * Configures GnAST AST generator and generates AST files for given XML Schema namespace.
   * 
   * @see net.sourceforge.czt.gnast.Gnast
   */
  @Override
  public void execute() throws MojoExecutionException
  {
    getLog().info("Generating AST for " + targetNamespace + ". This may take some time.");
    
    if (project != null) {
      project.addCompileSourceRoot(outputDirectory.getPath());
    }
    
    Set<URL> allSchemas = new HashSet<URL>();
    allSchemas.addAll(Gnast.schemaDirToURL(sourceDirectory));
    allSchemas.addAll(locateResources(sourceSchemas));
    
    if (allSchemas.isEmpty()) {
      throw new MojoExecutionException("No XML schema source files found. "
          + "They must be indicated either as sourceDirectory (" + sourceDirectory + ") "
          + "or as sourceSchemas (" + sourceSchemas + ")");
    }

    GnastBuilder config = new GnastBuilder()
        .templates(locateResources(templates))
        .sourceSchemas(allSchemas)
        .namespace(targetNamespace);

    if (outputDirectory != null) {
      config = config.destination(outputDirectory);
    }
    
    URL mappingFile = locateResource(mappingFileLocation);
    if (mappingFile != null) {
      config = config.mapping(mappingFile);
    }

    if (addAstFinaliser != null) {
      config = config.finalizers(addAstFinaliser.booleanValue());
    }

    if (verbose) {
      config = config.verbosity(Level.FINER);
    }
    
    if (buildContext != null) {
      config = config.buildContext(buildContext);
    }

    // create the generator and launch it
    try {
      
      Gnast gnast = config.create();
      gnast.generate();
      
    } catch (Exception ex) {
      // catch any exceptions and report as Maven ones
      throw new MojoExecutionException("GnAST code generation failed", ex);
    }

  }
  
  private List<URL> locateResources(Collection<String> locations) throws MojoExecutionException {
    List<URL> urls = new ArrayList<URL>();
    for (String location : locations) {
      urls.add(locateResource(location));
    }
    
    return urls;
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
