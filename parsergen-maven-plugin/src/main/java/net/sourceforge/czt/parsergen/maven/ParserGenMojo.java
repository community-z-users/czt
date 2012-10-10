/*
  Copyright (C) 2006, 2007, 2012  Petra Malik, Andrius Velykis
  
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
import java.io.FileInputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;
import org.sonatype.plexus.build.incremental.BuildContext;
import org.sonatype.plexus.build.incremental.DefaultBuildContext;

import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
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
  
  /**
   * @parameter expression="${project.build.directory}/generated-sources/parsergen"
   * @required
   */
  private File outputDirectory;
  
  /**
   * @parameter alias="templateFile"
   * @required
   */
  private List<File> templates = new ArrayList<File>();
  
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
      
      boolean forceGenerate = !outputDirectory.exists();

      String addExpr = toAddExpr(addNodes);

      for (File templateFile : templates) {
        
        // generate if it is fresh, or if the template file has changed
        boolean generate = forceGenerate || buildContext.hasDelta(templateFile);
        if (!generate) {
          continue;
        }

        String templateName = dropExtension(templateFile.getName());

        String targetClassName = className != null ? className : templateName;

        String targetFile = outputDirectory + "/" +
            packageName.replace('.', File.separatorChar) + "/" + 
            targetClassName + "." + fileExtension;

        generate(new File(targetFile), templateFile, targetClassName, packageName, addExpr);
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

  private String toAddExpr(String addNodes) {
    
    String[] splitNodes = addNodes.split(",");
    
    StringBuilder out = new StringBuilder();
    
    for (String addNode : splitNodes) {
      out.append("{");
      out.append(addNode.trim());
      out.append("}");
    }
    
    return out.toString();
  }
  
  private String dropExtension(String name) {
    int lastDot = name.lastIndexOf(".");
    if (lastDot >= 0) {
      return name.substring(0, lastDot);
    } else {
      return name;
    }
  }

  private void generate(File outFile,
                        File templateFile,
                        String className,
                        String packageName,
                        String addExpr)
    throws Exception
  {
    
    if (! outFile.getParentFile().exists()) {
      outFile.getParentFile().mkdirs();
    }
    
    OutputStream outputStream = buildContext.newFileOutputStream(outFile);
    
    try {
      Transformer t = getFactory().newTransformer(getTransformer());
      t.setParameter("class", className);
      t.setParameter("package", packageName);
      t.setParameter("add", addExpr);
      t.transform(new StreamSource(new FileInputStream(templateFile)),
                  new StreamResult(outputStream));
    }
    catch (TransformerConfigurationException e) {
      final String message = "Error generating file " + outFile;
      throw new MojoExecutionException(message, e);
    }
  }

  public Source getTransformer()
    throws Exception
  {
    final String name = "/transformer/template2text.xsl";
    return new StreamSource(getClass().getResource(name).openStream());
  }

}
