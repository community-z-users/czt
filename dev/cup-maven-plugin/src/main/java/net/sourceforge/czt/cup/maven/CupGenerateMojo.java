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
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import java_cup.ErrorManager;
import java_cup.Main;
import java_cup.ErrorManager.CupLogMessage;
import java_cup.runtime.ComplexSymbolFactory.Location;

import org.apache.maven.model.Resource;
import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.Component;
import org.apache.maven.plugins.annotations.LifecyclePhase;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.Parameter;
import org.apache.maven.project.MavenProject;
import org.sonatype.plexus.build.incremental.BuildContext;
import org.sonatype.plexus.build.incremental.DefaultBuildContext;


/**
 * Goal which generates parser source files from the given CUP parser specifications (*.cup).
 * <p>
 * Can be configured using all standalone CUP parser generator options.
 * </p>
 *
 * @author Andrius Velykis
 */
@Mojo(name = "generate", threadSafe = false, 
      defaultPhase = LifecyclePhase.GENERATE_SOURCES)
public class CupGenerateMojo extends AbstractMojo
{
  
  private static final String CUP_EXTENSION = ".cup";
  
  /**
   * The directory containing CUP specification files (*.cup).
   */
  @Parameter( property = "cup.sourceDirectory", defaultValue = "${project.basedir}/src/main/cup" )
  private File sourceDirectory;

  /**
   * The directory where CUP should generate parser and symbol files.
   */
  @Parameter( property = "cup.outputDirectory",
              defaultValue = "${project.build.directory}/generated-sources/cup" )
  private File outputDirectory;
  
  /**
   * Package name.
   * <p>
   * Specify that the parser and sym classes are to be placed in the named package. By default, no
   * package specification is put in the generated code (hence the classes default to the special
   * "unnamed" package).
   * </p>
   */
  @Parameter( property = "cup.packageName" )
  private String packageName;
  
  /**
   * Generated parser class name.
   * <p>
   * Output parser and action code into a file (and class) with the given name. If not given, CUP
   * file name will be used as the class name.
   * </p>
   */
  @Parameter( property = "cup.className" )
  private String className;
  
  /**
   * Specify type arguments for parser class.
   */
  @Parameter( property = "cup.typeArgs" )
  private String typeArgs;
  
  /**
   * Generated symbols class name.
   * <p>
   * Output the symbol constant code into a class with the given name instead of the default of
   * "Sym".
   * </p>
   */
  @Parameter( property = "cup.symbolsName", defaultValue = "Sym" )
  private String symbolsName;

  /**
   * Outputs the symbol constant code as an {@code interface} rather than as a {@code class}.
   */
  @Parameter( property = "cup.symbolsInterface", defaultValue = "false" )
  private boolean symbolsInterface;
  
  /**
   * Place constants for non-terminals into the symbol constant class. The parser does not need
   * these symbol constants, so they are not normally output. However, it can be very helpful to
   * refer to these constants when debugging a generated parser.
   */
  @Parameter( property = "cup.nontermsToSymbols", defaultValue = "false" )
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
   */
  @Parameter( property = "cup.expectedConflicts", defaultValue = "0" )
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
   */
  @Parameter( property = "cup.compactRed", defaultValue = "false" )
  private boolean compactRed;

  /**
   * Suppress all warning messages (as opposed to error messages) produced by the system.
   */
  @Parameter( property = "cup.noWarn", defaultValue = "false" )
  private boolean noWarn;
  
  /**
   * Suppress printing a summary listing such things as the number of terminals, non-terminals,
   * parse states, etc. at the end of the generation.
   */
  @Parameter( property = "cup.noSummary", defaultValue = "false" )
  private boolean noSummary;

  /**
   * Print short messages indicating progress through various parts of the parser generation
   * process.
   */
  @Parameter( property = "cup.showProgress", defaultValue = "false" )
  private boolean showProgress;
  
  /**
   * Output a human readable dump of the grammar. 
   */
  @Parameter( property = "cup.dumpGrammar", defaultValue = "false" )
  private boolean dumpGrammar;
  
  /**
   * Output a human readable dump of the constructed parse states (often needed to resolve parse
   * conflicts).
   */
  @Parameter( property = "cup.dumpStates", defaultValue = "false" )
  private boolean dumpStates;

  /**
   * Output a human readable dump of the parse tables (rarely needed).
   */
  @Parameter( property = "cup.dumpTables", defaultValue = "false" )
  private boolean dumpTables;
  
  /**
   * Add detailed timing statistics to the normal summary of results.
   */
  @Parameter( property = "cup.timeSummary", defaultValue = "false" )
  private boolean timeSummary;
  
  /**
   * Output internal debugging information about the system as it runs.
   */
  @Parameter( property = "cup.debug", defaultValue = "false" )
  private boolean debug;
  
  /**
   * Do not generate code to propagate the left and right hand values of terminals to non-terminals,
   * and then from non-terminals to other terminals. If the left and right values aren't going to be
   * used by the parser, then it will save some runtime computation to not generate these position
   * propagations. This option also keeps the left and right label variables from being generated,
   * so any reference to these will cause an error.
   */
  @Parameter( property = "cup.noPositions", defaultValue = "false" )
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
   */
  @Parameter( property = "cup.noScanner", defaultValue = "false" )
  private boolean noScanner;
  
  /**
   * Output parser tables to external files.
   * <p>
   * The external parser tables are normally encoded in the generated parser file. This option
   * allows outputting them to an external file, which is loaded by the generated parser
   * during runtime. The files are named as the parser tables, e.g. "action_table.dat".
   * </p>
   * <p>
   * If the parser tables are too large, they are always written to an external file, despite
   * this option here. This is to avoid "code too large" Java compilation errors, caused by
   * the initialisation code (the parser table String) being too large. This option allows
   * outputting all tables to external files, thus minimising parser class footprint.
   * </p>
   */
  @Parameter( property = "cup.externalTables", defaultValue = "false" )
  private boolean externalTables;
  
  /**
   * Suppress Java warnings in parser generated code locally when needed.
   * <p>
   * CUP produces generic Java code, some of which doesn't get used. For instance, the left/right
   * integer location information for every terminal in productions are always generated, even if
   * they are never used. This creates a series of unused warnings that need removing. Another 
   * example is when some of the terminal symbols contain elements with generic types. This creates
   * unchecked warnings at various places where such generic non-terminal types appear. At this 
   * stage it is needed to add an unchecked cast warning suppression. 
   * </p>
   * <p>
   * By default this flag is false, and all warnings are added. If set to true, our specific warning
   * suppression is added instead. Warning suppression is added locally, so as to not hide any dead
   * code or unchecked warning from user code. This is a local warning suppression.
   * </p>
   */
  @Parameter( property = "cup.suppressGeneratedJavaWarningsUnchecked", defaultValue = "false" )
  private boolean suppressGeneratedJavaWarningsUnchecked;
  
  /**
   * Suppress Java warnings in parser generated code globally.
   * <p>
   * Suppress any unused code warnings from CUP action class globally. 
   * TODO: make it local to each left/right assignment eventually
   * </p>
   */
  @Parameter( property = "cup.suppressGeneratedJavaWarningsUnused", defaultValue = "false" )
  private boolean suppressGeneratedJavaWarningsUnused;
  
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
   * Generates parser files for all CUP specifications found in source directory.
   */
  @Override
  public void execute()
    throws MojoExecutionException
  {
    if (project != null)
    {
      project.addCompileSourceRoot(outputDirectory.getPath());
      
      // also add the output directory *.dat files as resources to the project,
      // otherwise they will not be picked up for compilation.
      // *.dat files are external parser tables
      Resource resource = new Resource();
      resource.setDirectory(outputDirectory.getPath());
      resource.addInclude("**/*.dat");
      project.addResource(resource);
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
    
//    // find source files (only changed ones for incremental)
//    Scanner fileScanner = buildContext.newScanner(sourceDirectory);
//    fileScanner.setIncludes(new String[] { "**/*" + CUP_EXTENSION });
//    fileScanner.scan();
//    
//    List<File> cupFiles = new ArrayList<File>();
//    for (String path : fileScanner.getIncludedFiles()) {
//      // convert paths to absolute
//      cupFiles.add(new File(sourceDirectory, path));
//    }
//    
//    return cupFiles;
    
    // a workaround for a problem in EclipseBuildContext (Eclipse m2e), where
    // resources are not refreshed between the invocations of separate builders.
    // So if the CUP source files were generated in the same iteration, this
    // plug-in does not see them.
    // As a workaround, look for physical files and check for their deltas.
    List<File> allCupFiles = getAllCupFiles(new File[] { sourceDirectory });
    List<File> changed = new ArrayList<File>(); 
    
    for (File file : allCupFiles) {
      if (buildContext.hasDelta(file)) {
        changed.add(file);
      }
    }
    
    return changed;
  }
  
  private List<File> getAllCupFiles(File[] files)
  {
    List<File> cupFiles = new ArrayList<File>();
    for (File file : files) {
      if (file.isDirectory()) {
        cupFiles.addAll(getAllCupFiles(file.listFiles()));
      }
      else if (file.getName().endsWith(CUP_EXTENSION)) {
        cupFiles.add(file);
      }
    }
    return cupFiles;
  }
  
  private void generateCup(File file) throws MojoExecutionException
  {
    getLog().debug("CUP: Processing " + file.getPath());
    
    // remove previous error/warning messages
    buildContext.removeMessages(file);

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
      if (!destDir.mkdirs())
      {
    	  throw new MojoExecutionException("Couldn't create directories for " + destDir.getName());
      }
    }

    File destFile = new File(destDir, className + ".java");
    File symbolsFile = new File(destDir, symbolsName + ".java");

    List<String> args = new ArrayList<String>();

    if (packageName != null) {
      args.add("-package");
      args.add(packageName);
    }
    //always non null? if (className != null) {
      args.add("-parser");
      args.add(className);
    //}
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
    // CZT extra flags
    if (externalTables) {
      args.add("-external_tables");
    }
    if (suppressGeneratedJavaWarningsUnchecked)
    {
      args.add("-suppress_generated_java_warnings_unchecked");
    }
    if (suppressGeneratedJavaWarningsUnused)
    {
      args.add("-suppress_generated_java_warnings_unused");
    }

    // target directory path
    args.add("-destdir");
    args.add(destDir.getAbsolutePath());

    // source file
    args.add(file.getAbsolutePath());

    try {
      // run generator
      Main.main(args.toArray(new String[args.size()]));
    }
    catch (Exception e) {
      throw new MojoExecutionException("CUP generation failed: " + e.getMessage(), e);
    }
    finally {
      logCupMessages(file);
    }

    // refresh generated parser and symbol files after generation
    refreshFile(destFile);
    refreshFile(symbolsFile);
    
    File[] listFiles = destDir.listFiles();
    if (listFiles != null)
    {
	    // refresh generated external parser tables (*.dat files)
	    for (File resourceFile : listFiles) {
	      if (resourceFile.getName().endsWith(".dat")) {
	        refreshFile(resourceFile);
	      }
	    }
    }
    else
    {
    	throw new MojoExecutionException("Couldn't get destination directory list of files - " + destDir.getName());
    }
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
	//FileReader fl = new FileReader(cupFile);; avoid default encoding
    BufferedReader reader = new BufferedReader(
    		new InputStreamReader(new FileInputStream(cupFile), StandardCharsets.US_ASCII));

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
  
  private void refreshFile(File targetFile)
  {
    buildContext.refresh(targetFile);
    getLog().info("CUP: generated " + targetFile);
  }
  
  private void logCupMessages(File targetFile)
  {
    ErrorManager log = ErrorManager.getManager();
    logCupMessages(targetFile, log.getFatals(), BuildContext.SEVERITY_ERROR);
    logCupMessages(targetFile, log.getErrors(), BuildContext.SEVERITY_ERROR);
    logCupMessages(targetFile, log.getWarnings(), BuildContext.SEVERITY_WARNING);
  }

  private void logCupMessages(File targetFile, List<CupLogMessage> msgs, int severity)
  {
    if (msgs.isEmpty()) {
      return;
    }

    for (CupLogMessage msg : msgs) {
      
      // only support location at the moment
      Location loc = msg.getLeftLoc();
      
      int line, column;
      if (loc != null) {
        line = loc.getLine();
        column = loc.getColumn();
      }
      else {
        line = 0;
        column = 0;
      }
      
      buildContext.addMessage(targetFile, line, column, msg.getMessage(), severity, null);
    }
  }
  
}
