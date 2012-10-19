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
import org.apache.maven.project.MavenProject;
import org.codehaus.plexus.resource.DefaultResourceManager;
import org.codehaus.plexus.resource.PlexusResource;
import org.codehaus.plexus.resource.ResourceManager;
import org.codehaus.plexus.resource.loader.ResourceNotFoundException;
import org.sonatype.plexus.build.incremental.BuildContext;

/**
 * @goal generate
 *
 * @author Petra Malik
 * @author Andrius Velykis
 */
public class GnastGenerateMojo
  extends AbstractMojo 
{
  /**
   * @parameter expression="${project.build.directory}/generated-sources/gnast"
   */
  private File outputDirectory;

  /**
   * @parameter alias="templateDirectory"
   * @required
   */
  private List<String> templates = new ArrayList<String>();
  
  /**
   * @parameter
   */
  private String mappingFileLocation;
  
  /**
   * @parameter
   */
  private Boolean addAstFinaliser;
  
  /**
   * @parameter
   */
  private boolean verbose;
  
  /**
   * The directory where all XML schema source files are located.
   * <p>
   * At least one of {@link #sourceDirectory} or {@link #sourceSchemas} must
   * be set to find the schemas.
   * </p>
   * 
   * @parameter
   */
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
   * 
   * @parameter alias="schemaLocation"
   */
  private List<String> sourceSchemas = new ArrayList<String>();
  
  /**
   * @parameter
   * @required
   */
  private String targetNamespace;

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
