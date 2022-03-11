/*
  Copyright 2006, 2007, 2012  Petra Malik, Andrius Velykis
  
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

package net.sourceforge.czt.parsergen.maven;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
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
import org.sonatype.plexus.build.incremental.DefaultBuildContext;

import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;

/**
 * Goal which generates source files for different CZT parser generators by splitting the
 * corresponding XML definition files.
 *
 * @author Andrius Velykis
 */
@Mojo(name = "generate", threadSafe = false, 
      defaultPhase = LifecyclePhase.GENERATE_SOURCES)
public class ParserGenMojo
  extends AbstractMojo
{
 
  private static final String TRANSFORMER_SOURCE = "/transformer/template2text.xsl";
  
  /**
   * The directory where ParserGen should place the generated files.
   */
  @Parameter( property = "parsergen.outputDirectory",
              defaultValue = "${project.build.directory}/generated-sources/parsergen" )
  private File outputDirectory;
  
  /**
   * The list of ParserGen XML template directory paths.
   * <p>
   * The files in template paths are sources from which files are generated.
   * </p>
   * <p>
   * Potential values are filesystem paths, URLs, or classpath resources.
   * This parameter is resolved as resource, URL, then file.
   * </p>
   * @see org.codehaus.plexus.resource.ResourceManager
   */
  @Parameter( required = true )
  private List<String> templates = new ArrayList<String>();
  
  /**
   * The parts of XML templates that will constitute the generated files.
   * <p>
   * Comma-separated list of add: nodes, e.g. to use content of
   * {@code <add:zeves>..</add:zeves>}, use {@code zeves} here.
   * </p>
   */
  @Parameter( property = "parsergen.addNodes", required = true )
  private String addNodes;
  
  /**
   * The package name for generated files: the files are nested in directory matching the parser
   * and the package property is used for XML transformer. 
   */
  @Parameter( property = "parsergen.packageName", required = true )
  private String packageName;
  
  /**
   * The file extension of generated files. It will be used instead of *.xml of source file.
   * <p>
   * Use this parameter to indicate whether it is Java, CUP, JFlex or other file being generated.
   * </p>
   */
  @Parameter( property = "parsergen.fileExtension", required = true )
  private String fileExtension;
  
  /**
   * The explicit class name of generated file.
   * <p>
   * If not set, the generated file will match source template file name.
   * </p>
   */
  @Parameter( property = "parsergen.className" )
  private String className;
  
  /**
   * Add the output directory as compile source to the Maven project.
   * <p>
   * Use this when generating Java files using ParserGen.
   * </p>
   */
  @Parameter( property = "parsergen.compileSource", defaultValue = "false" )
  private boolean compileSource;
  
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


  // lazily initialised to avoid if nothing is generated
  private volatile TransformerFactory factory;

  private TransformerFactory getFactory()
  {
    if (factory == null) {
      synchronized (this) {
        if (factory == null) {
          factory = TransformerFactory.newInstance();
        }
      }
    }
    return factory;
  }

  /**
   * Transforms the source templates into generated files.
   */
  @Override
  public void execute()
    throws MojoExecutionException
  {
    
    if (buildContext == null) {
      // non-incremental context by default
      buildContext = new DefaultBuildContext();
    }
    
    try {

      if (compileSource && project != null) {
        project.addCompileSourceRoot(outputDirectory.getPath());
      }
      
      // force generation on a non-incremental build
      boolean forceGenerate = !buildContext.isIncremental() || !outputDirectory.exists();

      String addExpr = toAddExpr(addNodes);

      for (String templateLocation : templates) {
        
        PlexusResource templateResource = locateResource(templateLocation);
        
        // generate if it is fresh, or if the template file has changed
        boolean generate = forceGenerate || hasDelta(templateResource);
        if (!generate) {
          continue;
        }

        String templateName = getFileName(templateResource.getName());

        String targetClassName = className != null ? className : templateName;

        String targetFile = outputDirectory + "/" +
            packageName.replace('.', File.separatorChar) + "/" + 
            targetClassName + "." + fileExtension;

        generate(new File(targetFile), templateResource, targetClassName, packageName, addExpr);
      }

    }
    catch (MojoExecutionException e) {
      throw e;
    }
    catch (Exception e) {
      e.printStackTrace();
      throw new MojoExecutionException("Transformation failed", e);
    }
  }
  
  private boolean hasDelta(PlexusResource resource) throws MojoExecutionException
  {
    try {
      File file = resource.getFile();
      if (file == null) {
        // not a file - no changes then
        return false;
      } else {
        return buildContext.hasDelta(file);
      }
    }
    catch (IOException e) {
      throw new MojoExecutionException("Invalid resource: " + resource.getName(), e);
    }
  }
  
  private PlexusResource locateResource(String resourceLocation) throws MojoExecutionException {
    
    if (resourceLocation == null) {
      return null;
    }
    
    if (locator == null) {
      locator = new DefaultResourceManager();
    }
    
    try {
      return locator.getResource(resourceLocation);
    }
    catch (ResourceNotFoundException e) {
      throw new MojoExecutionException("Cannot find resource " + resourceLocation, e);
    }
    
  }

  private String toAddExpr(String addNodes)
  {

    String[] splitNodes = addNodes.split(",");

    StringBuilder out = new StringBuilder();

    for (String addNode : splitNodes) {
      out.append("{");
      out.append(addNode.trim());
      out.append("}");
    }

    return out.toString();
  }

  /**
   * Extracts file name (without extension) from a file path.
   * 
   * @param path
   * @return
   */
  private String getFileName(String path)
  {
    // try both backslashes, e.g. for windows paths?
    int lastSep1 = path.lastIndexOf("/");
    int lastSep2 = path.lastIndexOf("\\");
    int lastSep = Math.max(lastSep1, lastSep2);

    String nameExt;
    if (lastSep >= 0) {
      nameExt = path.substring(lastSep + 1);
    } else {
      nameExt = path;
    }

    int lastDot = nameExt.lastIndexOf(".");
    if (lastDot >= 0) {
      return nameExt.substring(0, lastDot);
    } else {
      return nameExt;
    }
  }

  private void generate(File outFile, PlexusResource templateResource,
      String className, String packageName, String addExpr) throws MojoExecutionException
  {
    
    if (! outFile.getParentFile().exists()) {
      if (! outFile.getParentFile().mkdirs()) 
      {
    	  throw new MojoExecutionException("Couldn't create directories for " + outFile.getParentFile().getName());
      }
    }
    
    URL transformerSourceUrl = ParserGenMojo.class.getResource(TRANSFORMER_SOURCE);
    if (transformerSourceUrl == null) {
      throw new MojoExecutionException("Cannot locate file at " + TRANSFORMER_SOURCE);
    }
    
    try {
      
      InputStream transformerStream = transformerSourceUrl.openStream();
      try {

        Transformer t = getFactory().newTransformer(new StreamSource(transformerStream));
        t.setParameter("class", className);
        t.setParameter("package", packageName);
        t.setParameter("add", addExpr);

        OutputStream outputStream = buildContext.newFileOutputStream(outFile);
        try {

          InputStream templateStream = templateResource.getInputStream();
          try {
            // perform the transformation - and close the streams afterwards
            t.transform(new StreamSource(templateStream), new StreamResult(outputStream));
          }
          finally {
            templateStream.close();
          }
        }
        finally {
          outputStream.close();
        }
      }
      finally {
        transformerStream.close();
      }
    }
    catch (TransformerException e) {
      final String message = "Error generating file " + outFile;
      throw new MojoExecutionException(message, e);
    }
    catch (IOException e) {
      final String message = "Error generating file " + outFile;
      throw new MojoExecutionException(message, e);
    }
  }

}
