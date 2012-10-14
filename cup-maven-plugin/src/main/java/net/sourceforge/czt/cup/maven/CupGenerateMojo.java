/*
  The MIT License

  Copyright 2012  Andrius Velykis

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
  THE SOFTWARE.
*/

package net.sourceforge.czt.cup.maven;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import java_cup.Main;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;
import org.codehaus.plexus.util.Scanner;
import org.sonatype.plexus.build.incremental.BuildContext;
import org.sonatype.plexus.build.incremental.DefaultBuildContext;

/**
 * @goal generate
 * @phase generate-sources
 * @description Java CUP Maven Plugin
 * 
 * @author Andrius Velykis
 */
public class CupGenerateMojo extends AbstractMojo
{
  
  private static final String CUP_EXTENSION = ".cup";
  
  /**
   * @parameter expression="${project.basedir}/src/main/cup"
   * @required
   */
  private File sourceDirectory;

  /**
   * @parameter expression="${project.build.directory}/generated-sources/cup"
   * @required
   */
  private File outputDirectory;
  
  /**
   * Package name.
   * <p>
   * Specify that the parser and sym classes are to be placed in the named package. By default, no
   * package specification is put in the generated code (hence the classes default to the special
   * "unnamed" package).
   * </p>
   * 
   * @parameter
   */
  private String packageName;
  
  /**
   * Generated parser class name.
   * <p>
   * Output parser and action code into a file (and class) with the given name. If not given, CUP
   * file name will be used as the class name.
   * </p>
   * 
   * @parameter
   */
  private String className;
  
  /**
   * Specify type arguments for parser class.
   * 
   * @parameter
   */
  private String typeArgs;
  
  /**
   * Generated symbols class name.
   * <p>
   * Output the symbol constant code into a class with the given name instead of the default of
   * "Sym".
   * </p>
   * 
   * @parameter default-value="Sym"
   */
  private String symbolsName;

  /**
   * Outputs the symbol constant code as an {@code interface} rather than as a {@code class}.
   * 
   * @parameter
   */
  private boolean symbolsInterface;
  
  /**
   * Place constants for non-terminals into the symbol constant class. The parser does not need
   * these symbol constants, so they are not normally output. However, it can be very helpful to
   * refer to these constants when debugging a generated parser.
   * 
   * @parameter
   */
  private boolean nontermsToSymbols;
  
  /**
   * During parser construction the system may detect that an ambiguous situation would occur at
   * runtime. This is called a conflict. In general, the parser may be unable to decide whether to
   * shift (read another symbol) or reduce (replace the recognized right hand side of a production
   * with its left hand side). This is called a shift/reduce conflict. Similarly, the parser may not
   * be able to decide between reduction with two different productions. This is called a
   * reduce/reduce conflict. Normally, if one or more of these conflicts occur, parser generation is
   * aborted. However, in certain carefully considered cases it may be advantageous to arbitrarily
   * break such a conflict. In this case CUP uses YACC convention and resolves shift/reduce
   * conflicts by shifting, and reduce/reduce conflicts using the "highest priority" production (the
   * one declared first in the specification). In order to enable automatic breaking of conflicts
   * the -expect option must be given indicating exactly how many conflicts are expected. Conflicts
   * resolved by precedences and associativities are not reported.
   * 
   * @parameter
   */
  private int expectedConflicts;
  
  /**
   * Including this option enables a table compaction optimization involving reductions. In
   * particular, it allows the most common reduce entry in each row of the parse action table to be
   * used as the default for that row. This typically saves considerable room in the tables, which
   * can grow to be very large. This optimization has the effect of replacing all error entries in a
   * row with the default reduce entry. While this may sound dangerous, if not down right incorrect,
   * it turns out that this does not affect the correctness of the parser. In particular, some
   * changes of this type are inherent in LALR parsers (when compared to canonical LR parsers), and
   * the resulting parsers will still never read past the first token at which the error could be
   * detected. The parser can, however, make extra erroneous reduces before detecting the error, so
   * this can degrade the parser's ability to do error recovery. (Refer to reference [2] pp. 244-247
   * or reference [3] pp. 190-194 for a complete explanation of this compaction technique.)
   * <p>
   * This option is typically used to work-around the java bytecode limitations on table
   * initialization code sizes. However, CUP 0.10h introduced a string-encoding for the parser
   * tables which is not subject to the standard method-size limitations. Consequently, use of this
   * option should no longer be required for large grammars.
   * </p>
   * 
   * @parameter
   */
  private boolean compactRed;

  /**
   * Suppress all warning messages (as opposed to error messages) produced by the system.
   * 
   * @parameter 
   */
  private boolean noWarn;
  
  /**
   * Suppress printing a summary listing such things as the number of terminals, non-terminals,
   * parse states, etc. at the end of the generation.
   * 
   * @parameter
   */
  private boolean noSummary;

  /**
   * Print short messages indicating progress through various parts of the parser generation
   * process.
   * 
   * @parameter
   */
  private boolean showProgress;
  
  /**
   * Output a human readable dump of the grammar. 
   * 
   * @parameter 
   */
  private boolean dumpGrammar;
  
  /**
   * Output a human readable dump of the constructed parse states (often needed to resolve parse
   * conflicts).
   * 
   * @parameter
   */
  private boolean dumpStates;

  /**
   * Output a human readable dump of the parse tables (rarely needed).
   * 
   * @parameter 
   */
  private boolean dumpTables;
  
  /**
   * Add detailed timing statistics to the normal summary of results.
   * 
   * @parameter
   */
  private boolean timeSummary;
  
  /**
   * Output internal debugging information about the system as it runs.
   * 
   * @parameter
   */
  private boolean debug;
  
  /**
   * Do not generate code to propagate the left and right hand values of terminals to non-terminals,
   * and then from non-terminals to other terminals. If the left and right values aren't going to be
   * used by the parser, then it will save some runtime computation to not generate these position
   * propagations. This option also keeps the left and right label variables from being generated,
   * so any reference to these will cause an error.
   * 
   * @parameter
   */
  private boolean noPositions;
  
  /**
   * Suppress {@link java_cup.runtime.Scanner} references.
   * <p>
   * CUP 0.10j introduced improved scanner integration and a new interface,
   * {@link java_cup.runtime.Scanner}. By default, the generated parser refers to this interface,
   * which means you cannot use these parsers with CUP runtimes older than 0.10j. If your parser
   * does not use the new scanner integration features, then you may suppress the
   * {@link java_cup.runtime.Scanner} references and allow compatibility with old runtimes. Not many
   * people should have reason to do this.
   * </p>
   * 
   * @parameter
   */
  private boolean noScanner;
  
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


  public void execute()
    throws MojoExecutionException
  {
    if (project != null)
    {
      project.addCompileSourceRoot(outputDirectory.getPath());
    }
    
    List<File> cupSourceFiles = getCupFiles();
    getLog().info("CUP: Processing " + cupSourceFiles.size() + " cup files");
    
    for (File file : cupSourceFiles) {
      generateCup(file);
    }
  }
  
  /**
   * Collects CUP files in the source directory (changed files only for incremental builds).
   * 
   * @return
   */
  private List<File> getCupFiles() {
    
    if (buildContext == null) {
      // non-incremental build context by default
      buildContext = new DefaultBuildContext();
    }
    
    // find source files (only changed ones for incremental)
    Scanner fileScanner = buildContext.newScanner(sourceDirectory);
    fileScanner.setIncludes(new String[] { "**/*" + CUP_EXTENSION });
    fileScanner.scan();
    
    List<File> cupFiles = new ArrayList<File>();
    for (String path : fileScanner.getIncludedFiles()) {
      // convert paths to absolute
      cupFiles.add(new File(sourceDirectory, path));
    }
    
    return cupFiles;
  }
  
  private void generateCup(File file) throws MojoExecutionException
  {
    getLog().debug("CUP: Processing " + file.getPath());

    String packageName = this.packageName;
    if (packageName == null) {
      try {
        packageName = getPackageName(file);
      }
      catch (IOException e) {
        // do not stop execution if package name resolution has problems
        getLog().debug(e);
      }
    }

    String className = this.className;
    if (className == null) {
      String fileName = file.getName();
      if (fileName.endsWith(CUP_EXTENSION)) {
        className = fileName.substring(0, fileName.length() - CUP_EXTENSION.length());
      }
      else {
        className = fileName;
      }
    }

    File destDir;
    if (packageName != null) {
      destDir = new File(outputDirectory, packageName.replace(".", "/"));
    }
    else {
      destDir = outputDirectory;
    }

    // create parent dirs
    if (!destDir.exists()) {
      destDir.mkdirs();
    }

    File destFile = new File(destDir, className + ".java");
    File symbolsFile = new File(destDir, symbolsName + ".java");

    List<String> args = new ArrayList<String>();

    if (packageName != null) {
      args.add("-package");
      args.add(packageName);
    }
    if (className != null) {
      args.add("-parser");
      args.add(className);
    }
    if (typeArgs != null) {
      args.add("-typearg");
      args.add(typeArgs);
    }
    if (symbolsName != null) {
      args.add("-symbols");
      args.add(symbolsName);
    }
    if (symbolsInterface) {
      args.add("-interface");
    }
    if (nontermsToSymbols) {
      args.add("-nonterms");
    }
    if (expectedConflicts > 0) {
      args.add("-expect");
      args.add(String.valueOf(expectedConflicts));
    }
    if (compactRed) {
      args.add("-compact_red");
    }
    if (noWarn) {
      args.add("-nowarn");
    }
    if (noSummary) {
      args.add("-nosummary");
    }
    if (showProgress) {
      args.add("-progress");
    }
    if (dumpGrammar) {
      args.add("-dump_grammar");
    }
    if (dumpStates) {
      args.add("-dump_states");
    }
    if (dumpTables) {
      args.add("-dump_tables");
    }
    if (timeSummary) {
      args.add("-time");
    }
    if (debug) {
      args.add("-debug");
    }
    if (noPositions) {
      args.add("-nopositions");
    }
    if (noScanner) {
      args.add("-noscanner");
    }

    // target directory path
    args.add("-destdir");
    args.add(destDir.getAbsolutePath());

    // source file
    args.add(file.getAbsolutePath());

    try {
      // run generator
      Main.main(args.toArray(new String[0]));
    }
    catch (Exception e) {
      throw new MojoExecutionException("CUP generation failed", e);
    }

    // refresh generated parser and symbol files after generation
    buildContext.refresh(destFile);
    buildContext.refresh(symbolsFile);

    getLog().info("CUP: generated " + destFile);
    getLog().info("CUP: generated " + symbolsFile);

  }

  /**
   * Retrieves the package name from file.
   * 
   * @param cupFile
   * @return
   * @throws IOException
   */
  private String getPackageName(File cupFile) throws IOException
  {
    BufferedReader reader = new BufferedReader(new FileReader(cupFile));

    try {

      String line = "";
      while ((line = reader.readLine()) != null) {
        int packageIndex = line.indexOf("package");
        if (packageIndex >= 0) {
          int packageNameIndex = packageIndex += 7;
          int packageNameEnd = line.indexOf(';', packageNameIndex);
          if (packageNameEnd >= packageNameIndex) {
            return line.substring(packageNameIndex, packageNameEnd).trim();
          }
        }
      }

    }
    finally {
      reader.close();
    }

    return null;
  }
}
