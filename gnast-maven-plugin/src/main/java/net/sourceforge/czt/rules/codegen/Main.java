/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.rules.codegen;

import java.io.File;
import java.io.FileWriter;
import java.io.Writer;
import java.util.Properties;
import java.util.Vector;
import org.w3c.dom.DOMConfiguration;
import org.w3c.dom.DOMError;
import org.w3c.dom.DOMErrorHandler;
import org.w3c.dom.bootstrap.DOMImplementationRegistry;

import org.apache.velocity.runtime.RuntimeInstance;
import org.apache.velocity.exception.ParseErrorException;
import org.apache.velocity.exception.ResourceNotFoundException;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.Template;

import org.apache.xerces.xs.*;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;

import net.sourceforge.czt.zml.Resources;

/**
 * @goal rulecodegen
 *
 * @author Petra Malik
 */
public class Main
  extends AbstractMojo 
{
  private static String PACKAGE_DIR = "net/sourceforge/czt/rules/ast/";

  /**
   * @parameter expression="${project.build.directory}/generated-sources/gnast"
   * @required
   */
  private String outputDirectory;

  /**
   * @parameter expression="${basedir}/src/codegen/vm"
   * @required
   */
  private String velocimacroDirectory;

  /**
   * @parameter expression="${project}"
   * @required
   */
  private MavenProject project;

  public void execute()
    throws MojoExecutionException
  {
    if (project != null )
    {
      project.addCompileSourceRoot(outputDirectory);
    }
    File outputDir = new File(outputDirectory);
    if (outputDir.exists())
    {
      getLog().info( "Code has already been generated" );
      return;
    }
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
      XSModel model = schemaLoader.loadURI(Resources.getZpattSchema().toString());

      RuntimeInstance velocity = new RuntimeInstance();
      Properties initProps = new Properties();
      initProps.put("file.resource.loader.path", velocimacroDirectory);
      velocity.init(initProps);
    
      XSNamedMap map = model.getComponents(XSTypeDefinition.COMPLEX_TYPE);
      Vector jokers = new Vector();
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
          String dest = outputDirectory + "/" + PACKAGE_DIR +
            "Prover" + name + ".java";
          write(velocity, dest, "Joker.vm", context);
          dest = outputDirectory + "/" + PACKAGE_DIR +
            "Prover" + name + "Binding.java";
          write(velocity, dest, "Binding.vm", context);
        }
      }
      final String dest =
        outputDirectory + "/" + PACKAGE_DIR + "ProverFactory.java";
      VelocityContext context = new VelocityContext();
      context.put("jokers", jokers);
      write(velocity, dest, "Factory.vm", context);
    }
    catch (Exception e) {
      e.printStackTrace();
      throw new MojoExecutionException(e.getMessage(), e);
    }
  }

  private static void write(RuntimeInstance velocity,
                            String destination,
                            String templateName,
                            VelocityContext context)
    throws Exception
  {
    File dest = new File(destination);
    System.err.println(destination);
    dest.getParentFile().mkdirs();
    dest.createNewFile();
    Writer writer = new FileWriter(dest);
    Template template = velocity.getTemplate(templateName);
    System.err.println("Writing file " + destination);
    template.merge(context, writer);
    writer.close();
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
