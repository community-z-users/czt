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
import java.net.URL;

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
      generate();
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
    generateCup("Parser", basePackage + "z", "{z}");
    generateCup("Parser", basePackage + "zpatt", "{zpatt}");
    generateCup("Parser", basePackage + "oz", "{oz}{ozz}");
    generateCup("Parser", basePackage + "tcoz", "{oz}{tcoz}");
    generateCup("Parser", basePackage + "circus", "{circus}");

    generateJava("LatexParser", basePackage + "z", "{z}");
    generateJava("LatexParser", basePackage + "zpatt", "{zpatt}");
    generateJava("LatexParser", basePackage + "oz", "{oz}");
    generateJava("LatexParser", basePackage + "tcoz", "{tcoz}");
    generateJava("LatexParser", basePackage + "circus", "{circus}");

    generateJava("UnicodeParser", basePackage + "z", "{z}");
    generateJava("UnicodeParser", basePackage + "zpatt", "{zpatt}");
    generateJava("UnicodeParser", basePackage + "oz", "{oz}");
    generateJava("UnicodeParser", basePackage + "tcoz", "{tcoz}");
    generateJava("UnicodeParser", basePackage + "circus", "{circus}");

    generateJFlex("Latex2Unicode", basePackage + "z", "{z}");
    generateJFlex("Latex2Unicode", basePackage + "zpatt", "{zpatt}");
    generateJFlex("Latex2Unicode", basePackage + "oz", "{oz}");
    generateJFlex("Latex2Unicode", basePackage + "tcoz", "{oz}{tcoz}");
    generateJFlex("Latex2Unicode", basePackage + "circus", "{circus}");

    generateJava("LatexToUnicode", basePackage + "z", "{z}");
    generateJava("LatexToUnicode", basePackage + "zpatt", "{zpatt}");
    generateJava("LatexToUnicode", basePackage + "oz", "{oz}");
    generateJava("LatexToUnicode", basePackage + "tcoz", "{tcoz}");
    generateJava("LatexToUnicode", basePackage + "circus", "{circus}");

    generateJava("LatexMarkupParser", basePackage + "z", "{z}");
    generateJava("LatexMarkupParser", basePackage + "zpatt", "{zpatt}");
    generateJava("LatexMarkupParser", basePackage + "oz", "{oz}");
    generateJava("LatexMarkupParser", basePackage + "tcoz", "{tcoz}");
    generateJava("LatexMarkupParser", basePackage + "circus", "{circus}");

    generateJava("LatexScanner", basePackage + "z", "{z}");
    generateJava("LatexScanner", basePackage + "zpatt", "{zpatt}");
    generateJava("LatexScanner", basePackage + "oz", "{oz}");
    generateJava("LatexScanner", basePackage + "tcoz", "{tcoz}");
    generateJava("LatexScanner", basePackage + "circus", "{circus}");

    generateJava("ParseUtils", basePackage + "z", "{z}");
    generateJava("ParseUtils", basePackage + "zpatt", "{zpatt}");
    generateJava("ParseUtils", basePackage + "oz", "{oz}");
    generateJava("ParseUtils", basePackage + "tcoz", "{tcoz}");
    generateJava("ParseUtils", basePackage + "circus", "{circus}");

    generateJava("UnicodeScanner", basePackage + "z", "{z}");
    generateJava("UnicodeScanner", basePackage + "zpatt", "{zpatt}");
    generateJava("UnicodeScanner", basePackage + "oz", "{oz}");
    generateJava("UnicodeScanner", basePackage + "tcoz", "{tcoz}");
    generateJava("UnicodeScanner", basePackage + "circus", "{circus}");

    generateJava("OperatorScanner", basePackage + "z", "{z}");
    generateJava("OperatorScanner", basePackage + "zpatt", "{zpatt}");
    generateJava("OperatorScanner", basePackage + "oz", "{oz}");
    generateJava("OperatorScanner", basePackage + "tcoz", "{oz}{tcoz}");
    generateJava("OperatorScanner", basePackage + "circus", "{circus}");

    generateJava("NewlineScanner", basePackage + "z", "{z}");
    generateJava("NewlineScanner", basePackage + "zpatt", "{zpatt}");
    generateJava("NewlineScanner", basePackage + "oz", "{oz}");
    generateJava("NewlineScanner", basePackage + "tcoz", "{oz}{tcoz}");
    generateJava("NewlineScanner", basePackage + "circus", "{circus}");

    generateJava("KeywordScanner", basePackage + "z", "{z}");
    generateJava("KeywordScanner", basePackage + "zpatt", "{zpatt}");
    generateJava("KeywordScanner", basePackage + "oz", "{oz}");
    generateJava("KeywordScanner", basePackage + "tcoz", "{oz}{tcoz}");
    generateJava("KeywordScanner", basePackage + "circus", "{circus}");

    generateJFlex("ContextFreeScanner", basePackage + "z", "{z}");
    generateJFlex("ContextFreeScanner", basePackage + "zpatt", "{zpatt}");
    generateJFlex("ContextFreeScanner", basePackage + "oz", "{oz}");
    generateJFlex("ContextFreeScanner", basePackage + "tcoz", "{oz}{tcoz}");
    generateJFlex("ContextFreeScanner", basePackage + "circus", "{circus}");

    generateJava("SmartScanner", basePackage + "z", "{z}");
    generateJava("SmartScanner", basePackage + "zpatt", "{zpatt}");
    generateJava("SmartScanner", basePackage + "oz", "{oz}");
    generateJava("SmartScanner", basePackage + "tcoz", "{z}{oz}");
    generateJava("SmartScanner", basePackage + "circus", "{circus}");

    generateJava("SymMap", basePackage + "zpatt", "{zpatt}");
    generateJava("SymMap", basePackage + "oz", "{oz}");
    generateJava("SymMap", basePackage + "tcoz", "{tcoz}");
    generateJava("SymMap", basePackage + "circus", "{circus}");
  }

  private void generatePrinter()
    throws Exception
  {
    generatePrintScanner();
    generatePrintParser();
  }

  private void generatePrintScanner()
    throws Exception
  {
    generateJFlex("ContextFreeScanner",
                 "net.sourceforge.czt.print.z",
                 "{print}");
    generateJFlex("ContextFreeScanner",
                 "net.sourceforge.czt.print.oz",
                 "{oz}{print}");
    generateJFlex("ContextFreeScanner",
                 "net.sourceforge.czt.print.circus",
                 "{circus}{print}");
    generateJava("SectHeadScanner",
                 "net.sourceforge.czt.print.z",
                 "{z}{print}");
    generateJava("SectHeadScanner",
                 "net.sourceforge.czt.print.oz",
                 "{oz}{print}");
    generateJava("SectHeadScanner",
                 "net.sourceforge.czt.print.circus",
                 "{circus}{print}");
  }

  private void generatePrintParser()
    throws Exception
  {
    final String basePackage = "net.sourceforge.czt.print.";
    generateCup("Unicode2Latex", basePackage + "z", "{z}");
    generateCup("Unicode2Latex",
    "Unicode2OldLatex", basePackage + "z", "{oldz}");
    generateCup("Unicode2Latex", basePackage + "oz", "{z}{oz}");
    generateCup("Unicode2Latex", basePackage + "circus", "{z}{circus}");
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
    if (! outFile.getParentFile().exists()) {
      outFile.getParentFile().mkdirs();
    }
    try {
      Transformer t = factory_.newTransformer(getTransformer());
      t.setParameter("class", className);
      t.setParameter("package", packageName);
      t.setParameter("add", addExpr);
      t.transform(getTemplate(template + ".xml"),
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

  public Source getTemplate(String template)
    throws Exception
  {
    final String name = "/templates/" + template;
    final URL url = getClass().getResource(name);
    if (url == null) {
      throw new MojoExecutionException("Cannot find resource " + name);
    }
    return  new StreamSource(url.openStream());
  }
}
