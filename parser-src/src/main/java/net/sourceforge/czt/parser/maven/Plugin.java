/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.parser.maven;

import java.io.File;
import java.io.FileOutputStream;
import java.net.URI;
import java.net.URL;
import java.net.URLConnection;
import java.util.Date;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;

import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;

/**
 * @goal generate
 * @phase generate-sources
 * @description Maven Parser Source Plugin
 */
public class Plugin
  extends AbstractMojo
{
  /**
   * @parameter expression="all"
   * @required
   */
  private String dialect;

  /**
   * @parameter expression="${project.build.directory}/generated-sources/parser-src"
   * @required
   */
  private String outputDirectory;

  /**
   * @parameter expression="${project.build.directory}/generated-sources/parser-src-cup"
   * @required
   */
  private String cupOutputDirectory;

  /**
   * @parameter expression="${project.build.directory}/generated-sources/parser-src-jflex"
   * @required
   */
  private String jflexOutputDirectory;
  
  /**
   * @parameter expression="${project.build.directory}/generated-sources/templates"
   * @required
   */
  private String templateDirectory;

  /**
   * @parameter expression="${project}"
   * @required
   */
  private MavenProject project;

  private TransformerFactory factory_ = TransformerFactory.newInstance();


  public void execute()
    throws MojoExecutionException
  {
    if (project != null) {
      project.addCompileSourceRoot(outputDirectory);
    }
    try {
      if ("all".equals(dialect)) {
        generate();
      }
      else if ("circus".equals(dialect)) {
        generateCircusParser("net.sourceforge.czt.parser.");
        generateCircusPrinter("net.sourceforge.czt.print.");
      }
      else if ("oz".equals(dialect)) {
        generateOzParser("net.sourceforge.czt.parser.");
        generateOzPrinter("net.sourceforge.czt.print.");
      }
      else if ("tcoz".equals(dialect)) {
        generateTcozParser("net.sourceforge.czt.parser.");
      }
      else if ("zpatt".equals(dialect)) {
        generateZpattParser("net.sourceforge.czt.parser.");
        generateZpattPrinter("net.sourceforge.czt.print.");
      }
      else {
        throw new MojoExecutionException("Unsupported dialect " + dialect);
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

  private void generate()
    throws Exception
  {
    generateParser();
    generatePrinter();
  }

  private void generateParser()
    throws Exception
  {
    final String basePackage = "net.sourceforge.czt.parser.";
    generateZParser(basePackage);
  }

  private void generateZParser(String basePackage)
    throws Exception
  {
    final String add = "{z}";
    final String packageName =  basePackage + "z";
    generateCup("Parser", packageName, add);
    generateJava("LatexParser", packageName, add);
    generateJava("UnicodeParser", packageName, add);
    generateJFlex("Latex2Unicode", packageName, add);
    generateJava("LatexToUnicode", packageName, add);
    generateJava("LatexMarkupParser", packageName, add);
    generateJava("LatexScanner", packageName, add);
    generateJava("ParseUtils", packageName, add);
    generateJava("UnicodeScanner", packageName, add);
    generateJava("OperatorScanner", packageName, add);
    generateJava("NewlineScanner", packageName, add);
    generateJava("KeywordScanner", packageName, add);
    generateJFlex("ContextFreeScanner", packageName, add);
    generateJava("SmartScanner", packageName, add);
  }

  private void generateZpattParser(String basePackage)
    throws Exception
  {
    final String add = "{zpatt}";
    final String packageName =  basePackage + "zpatt";
    generateCup("Parser", packageName, add);
    generateJava("LatexParser", packageName, add);
    generateJava("UnicodeParser", packageName, add);
    generateJFlex("Latex2Unicode", packageName, add);
    generateJava("LatexToUnicode", packageName, add);
    generateJava("LatexMarkupParser", packageName, add);
    generateJava("LatexScanner", packageName, add);
    generateJava("ParseUtils", packageName, add);
    generateJava("UnicodeScanner", packageName, add);
    generateJava("OperatorScanner", packageName, add);
    generateJava("NewlineScanner", packageName, add);
    generateJava("KeywordScanner", packageName, add);
    generateJFlex("ContextFreeScanner", packageName, add);
    generateJava("SmartScanner", packageName, add);
    generateJava("SymMap", packageName, add);
  }

  private void generateOzParser(String basePackage)
    throws Exception
  {
    final String add = "{oz}";
    final String packageName =  basePackage + "oz";
    generateJava("LatexParser", packageName, add);
    generateCup("Parser", packageName, "{oz}{ozz}");
    generateJava("UnicodeParser", packageName, add);
    generateJFlex("Latex2Unicode", packageName, add);
    generateJava("LatexToUnicode", packageName, add);
    generateJava("LatexMarkupParser", packageName, add);
    generateJava("LatexScanner", packageName, add);
    generateJava("ParseUtils", packageName, add);
    generateJava("UnicodeScanner", packageName, add);
    generateJava("OperatorScanner", packageName, add);
    generateJava("NewlineScanner", packageName, add);
    generateJava("KeywordScanner", packageName, add);
    generateJFlex("ContextFreeScanner", packageName, add);
    generateJava("SmartScanner", packageName, add);
    generateJava("SymMap", packageName, add);
  }

  private void generateTcozParser(String basePackage)
    throws Exception
  {
    final String packageName =  basePackage + "tcoz";
    generateCup("Parser", packageName, "{oz}{tcoz}");
    generateJava("LatexParser", packageName, "{tcoz}");
    generateJava("UnicodeParser", packageName, "{tcoz}");
    generateJFlex("Latex2Unicode", packageName, "{oz}{tcoz}");
    generateJava("LatexToUnicode", packageName, "{tcoz}");
    generateJava("LatexMarkupParser", packageName, "{tcoz}");
    generateJava("LatexScanner", packageName, "{tcoz}");
    generateJava("ParseUtils", packageName, "{tcoz}");
    generateJava("UnicodeScanner", packageName, "{tcoz}");
    generateJava("OperatorScanner", packageName, "{oz}{tcoz}");
    generateJava("NewlineScanner", packageName, "{oz}{tcoz}");
    generateJava("KeywordScanner", packageName, "{oz}{tcoz}");
    generateJFlex("ContextFreeScanner", packageName, "{oz}{tcoz}");
    generateJava("SmartScanner", packageName, "{z}{oz}");
    generateJava("SymMap", packageName, "{tcoz}");
  }

  private void generateCircusParser(String basePackage)
    throws Exception
  {
    final String add = "{circus}";
    final String packageName =  basePackage + "circus";
    generateCup("Parser", packageName, "{circus}");
    generateJava("LatexParser", packageName, add);
    generateJava("UnicodeParser", packageName, add);
    generateJFlex("Latex2Unicode", packageName, add);
    generateJava("LatexToUnicode", packageName, add);
    generateJava("LatexMarkupParser", packageName, add);
    generateJava("LatexScanner", packageName, add);
    generateJava("ParseUtils", packageName, add);
    generateJava("UnicodeScanner", packageName, add);
    generateJava("OperatorScanner", packageName, add);
    generateJava("NewlineScanner", packageName, add);
    generateJava("KeywordScanner", packageName, add);
    generateJFlex("ContextFreeScanner", packageName, add);
    generateJava("SmartScanner", packageName, add);
    generateJava("SymMap", packageName, add);
  }    

  private void generatePrinter()
    throws Exception
  {
    final String basePackage = "net.sourceforge.czt.print.";
    generateZPrinter(basePackage);
  }

  private void generateZPrinter(String basePackage)
    throws Exception
  {
    generateCup("Unicode2Latex", basePackage + "z", "{z}");
    generateCup("Unicode2Latex",
    "Unicode2OldLatex", basePackage + "z", "{oldz}");
    generateJFlex("ContextFreeScanner",
                 "net.sourceforge.czt.print.z",
                 "{print}");
    generateJava("SectHeadScanner",
                 "net.sourceforge.czt.print.z",
                 "{z}{print}");
  }

  private void generateZpattPrinter(String basePackage)
    throws Exception
  {
    generateCup("Unicode2Latex", basePackage + "zpatt", "{z}{zpatt}");
    generateJFlex("ContextFreeScanner",
                  "net.sourceforge.czt.print.zpatt",
                  "{zpatt}{print}");
    generateJava("SectHeadScanner",
                 "net.sourceforge.czt.print.zpatt",
                 "{zpatt}{print}");
  }

  private void generateOzPrinter(String basePackage)
    throws Exception
  {
    generateCup("Unicode2Latex", basePackage + "oz", "{z}{oz}");
    generateJFlex("ContextFreeScanner",
                 "net.sourceforge.czt.print.oz",
                 "{oz}{print}");
    generateJava("SectHeadScanner",
                 "net.sourceforge.czt.print.oz",
                 "{oz}{print}");
  }

  private void generateCircusPrinter(String basePackage)
    throws Exception
  {
    generateCup("Unicode2Latex", basePackage + "circus", "{z}{circus}");
    generateJFlex("ContextFreeScanner",
                 "net.sourceforge.czt.print.circus",
                 "{circus}{print}");
    generateJava("SectHeadScanner",
                 "net.sourceforge.czt.print.circus",
                 "{circus}{print}");
  }

  private void generateJava(String className,
                            String packageName,
                            String addExpr)
    throws Exception
  {
    final String output = outputDirectory + "/" +
      packageName.replace('.', File.separatorChar) + "/" +
      className + ".java";
    generate(output, className, className, packageName, addExpr);
  }

  private void generateCup(String className,
                           String packageName,
                           String addExpr)
    throws Exception
  {
    generateCup(className, className, packageName, addExpr);
  }

  private void generateCup(String template,
                           String className,
                           String packageName,
                           String addExpr)
    throws Exception
  {
    final String output = cupOutputDirectory + "/" +
      packageName.replace('.', File.separatorChar) + "/" +
      className + ".cup";
    generate(output, template, className, packageName, addExpr);
  }

  private void generateJFlex(String className,
                             String packageName,
                             String addExpr)
    throws Exception
  {
    generateJFlex(className, className, packageName, addExpr);
  }

  private void generateJFlex(String template,
                             String className,
                             String packageName,
                             String addExpr)
    throws Exception
  {
    final String output = jflexOutputDirectory + "/" +
      packageName.replace('.', File.separatorChar) + "/" +
      className + ".jflex";
    generate(output, template, className, packageName, addExpr);
  }

  private void generate(String output,
                        String template,
                        String className,
                        String packageName,
                        String addExpr)
    throws Exception
  {
    final File outFile = new File(output);
    final URL url = getTemplate(template + ".xml");
    final URLConnection connection = url.openConnection();             
    getLog().info("Checking file dates:\n\t" + new Date(outFile.lastModified()) + 
          "= " + output + "\n\t" + new Date(connection.getLastModified()) + "= " +
          connection);
    if (outFile.exists() &&
        outFile.lastModified() >= connection.getLastModified()) {      
      getLog().info("File " + output + " is up-to-date.");
      return;
    }
    if (! outFile.getParentFile().exists()) {
      outFile.getParentFile().mkdirs();
    }
    try {
      Transformer t = factory_.newTransformer(getTransformer());
      t.setParameter("class", className);
      t.setParameter("package", packageName);
      t.setParameter("add", addExpr);
      t.transform(new StreamSource(connection.getInputStream()),
                  new StreamResult(new FileOutputStream(output)));
    }
    catch (TransformerConfigurationException e) {
      final String message = "Error generating file " + output;
      throw new MojoExecutionException(message, e);
    }
  }

  public Source getTransformer()
    throws Exception
  {
    final String name = "/transformer/template2text.xsl";
    return new StreamSource(getClass().getResource(name).openStream());
  }

  public URL getTemplate(String template)
    throws Exception
  {    
    String name = templateDirectory + "/" + template;
    getLog().info("Retrieving template " + name);
    URL url = null;
    File file = new File(name);
    if (file.exists()) {      
      URI uri = file.toURI();
      if (uri == null) {
        throw new MojoExecutionException("Cannot find resource " + name);
      }
      url = uri.toURL();
    }
    if (url == null) {
      getLog().warn("Failed to get template at \"templateDirectory\" location. Trying reposity jar file instead.");          
      name = "/templates/" + template;
      getLog().info("Retrieving template " + name);
      url = getClass().getResource(name);          
      if (url == null) {
        throw new MojoExecutionException("Cannot find resource " + name);
      }    
    }
    return url;
  }
}
