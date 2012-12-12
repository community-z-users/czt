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
 * @goal generate
 * @phase generate-sources
 * @description CZT Parser Generator Maven Plugin
 * 
 * @author Andrius Velykis
 */
public class ParserGenMojo
  extends AbstractMojo
{
 
  private static final String TRANSFORMER_SOURCE = "/transformer/template2text.xsl";
  
  /**
   * @parameter expression="${project.build.directory}/generated-sources/parsergen"
   * @required
   */
  private File outputDirectory;
  
  /**
   * @parameter
   * @required
   */
  private List<String> templates = new ArrayList<String>();
  
  /**
   * Comma-separated list of add: nodes
   * @parameter
   * @required
   */
  private String addNodes;
  
  /**
   * @parameter
   * @required
   */
  private String packageName;
  
  /**
   * @parameter
   * @required
   */
  private String fileExtension;
  
  /**
   * @parameter
   */
  private String className;
  
  /**
   * @parameter
   */
  private boolean compileSource = false;
  
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
      outFile.getParentFile().mkdirs();
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