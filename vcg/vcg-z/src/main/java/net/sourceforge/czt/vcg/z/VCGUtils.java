/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the czt project.
 * 
 * The czt project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The czt project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with czt; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.SortedMap;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.print.z.LatexPrinterPropertyKeys;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.util.DefinitionTable;
import net.sourceforge.czt.vcg.util.DefinitionTableService;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.WarningManager.WarningOutput;

/**
 *
 * @param <R> old parameter for VCEnvAnn. No longer needed.
 * @author Leo Freitas
 * @date Dec 25, 2010
 */
public abstract class VCGUtils<//R,
								T, B> implements VCGPropertyKeys
{

  /* UTILITY CLASS SETUP METHODS */

  private VCG<//R, 
  				T, B> vcg_;
  private boolean debug_;
  private Dialect extension_;

  protected VCGUtils()
  {
    vcg_ = null;
    debug_ = false;
    extension_ = SectionManager.DEFAULT_EXTENSION;
  }

  protected abstract VCG<//R, 
  						T, B> createVCG();

  public final VCG<//R, 
  					T, B> getVCG()
  {
    if (vcg_ == null)
    {
      vcg_ = createVCG();
    }
    return vcg_;
  }

  public final boolean isDebugging()
  {
    return debug_;
  }

  /* UTILITY CLASS VCG METHODS */

  /**
   * This method should be called as few times as possible, as it returns
   * a brand new section manager . It is to be used by the top-level DC application only
   * @param extension the CZT extension to use
   * @return a fresh new section manager.
   * @throws VCGException
   */
  public SectionManager createSectionManager(Dialect extension) throws VCGException
  {
    // if null or for a different dialect, get a new one; CHANGED: even if same dialect, get new one to avoid duplicated entries?
    if (getVCG().getManager() == null /*|| (!getVCG().getManager().getDialect().equals(extension))*/)
    {
      BaseFactory.resetInstanceCounter();
      SectionManager manager = new SectionManager(extension);
      setSectionManager(manager);
    }
    return getVCG().getManager();
  }

  protected void setDefaultCommands(SectionManager manager)
  {
    if (manager.getCommand(getVCG().getVCEnvAnnClass()) == null)
    {
      manager.putCommand(getVCG().getVCEnvAnnClass(), getCommand());
    }
    // override the Z DefTable cmd
    manager.putCommand(DefinitionTable.class, DefinitionTableService.getCommand(manager));
  }

  /**
   * To reuse a section manager, set it as such, if VCG not already set.
   * This methods is useful for top-level applications that already have a section
   * manager (e.g., jEdit). It sets default commands needed as well as default properties
   * before configuring the manager and the VCG. If these properties change, the
   * VCG needs to be reconfigured (e.g., {@link #getVCG().config() }).
   * @param manager
   * @throws VCGException
   */
  public void setSectionManager(SectionManager manager) throws VCGException
  {
    setDefaultCommands(manager);
    setDefaultProperties(manager);
    getVCG().setSectionManager(manager);
  }

  /**
   * Sets any utility properties to the section manager and calls the VCG default properties as well.
   * @param manager
   */
  protected void setDefaultProperties(SectionManager manager)
  {
    manager.setProperty(LatexPrinterPropertyKeys.PROP_LATEXPRINTER_WRAPPING,
      String.valueOf(latexOutputWrappingDefault()));
    manager.setProperty(PROP_VCGU_PREFERRED_OUTPUT_MARKUP, Markup.LATEX.toString());
    getVCG().setDefaultProperties(manager);
  }

  public boolean isConfigured()
  {
    return getVCG().isConfigured();
  }

  /* TOP-LEVEL UTILITY METHODS FOR DERIVED CLASSES */

  /**
   * Get a Command object for use in SectionManager
   *
   * @return A command for VC generation of Z sections.
   */
  public abstract Command getCommand();

  /**
   * Top-level CZT UI tool name. e.g., "zedvcgdc" for Z domain checks.
   * @return
   */
  public abstract String getToolName();

  protected void printToolUsage()
  {
    // nothing extra here
  }

  protected String printToolDefaultFlagsUsage()
  {
    return ((printBenchmarkDefault() ? "-b " : "")
              + (getVCG().isProcessingParents() ? "-p " : "")
              + (getVCG().isAddingTrivialVC() ? "-t " : "")
              + (getVCG().getVCCollector().getTransformer().isApplyingTransformer() ? "-r " : "")
              + (getVCG().isRaisingTypeWarnings() ? "-w " : "")
              + (getVCG().isCheckingDefTblConsistency() ? "-y " : "")
              + ("-e" + cztExtensionDefault().toString())
              + ("-m" + preferedMarkupDefault()).trim());
  }

  /** Print a usage message to System.err, describing the
   *  command line arguments accepted by main.
   */
  protected final void printUsage()
  {
    System.err.println("usage: " + getToolName() + " [-bptrw] filename1 ... filenameN");
    System.err.println("flags: -b     print execution benchmarks.");
    System.err.println("       -p     process parent sections.");
    System.err.println("       -t     add trivial VCs.");
    System.err.println("       -r     apply term transformers.");
    System.err.println("       -s     show warnings (cannot show when hiding!)");
    System.err.println("       -h     hide warnings (cannot hide when raising!)");
    System.err.println("       -w     raise type warnings as errors.");
    System.err.println("       -y     check def table consistency.");
    System.err.println("       -mX    prefered markup to print results");
    System.err.println("              where X=LATEX, UNICODE, XML");
    System.err.println("       -eX    prefered czt extension to use");
    System.err.println("              where X=Z, OZ, CIRCUS, ZEVES, etc.");
    System.err.println("       -i <l> list of parents to ignore.");
    System.err.println("              a path-separated list of section names");
    System.err.println("              (e.g., -cp ./tests" + File.pathSeparator + "/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");
    System.err.println("      -cp <l> specify the value for czt.path as");
    System.err.println("              a semicolon-separated list of dirs");
    System.err.println("              (e.g., -cp ./tests" + File.pathSeparator + "/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");
    printToolUsage();
    System.err.println("\n");
    System.err.println("Default flags are: \""
                       + printToolDefaultFlagsUsage().trim()
                       + "\"\n");
  }

  protected boolean printBenchmarkDefault()
  {
    return PROP_VCGU_PRINT_BENCHMARK_DEFAULT;
  }

  protected String cztPathDefault()
  {
    return null;
  }

  protected Dialect cztExtensionDefault()
  {
    return Dialect.Z;
  }

  protected Markup preferedMarkupDefault()
  {
    return PROP_VCGU_PREFERRED_MARKUP_DEFAULT;
  }

  protected boolean latexOutputWrappingDefault()
  {
    return PROP_VCGU_LATEX_OUTPUT_WRAPPING_DEFAULT;
  }

  public Dialect getExtension()
  {
    return extension_;
  }

  public void setExtension(Dialect ext)
  {
 	assert ext != null;
    extension_ = ext;
  }

  protected boolean isKnownArg(String arg)
  {
    return false;
  }

  protected void processArg(String arg)
  {
    // do nothing
  }

  protected void processCollectedProperties()
  {
    // do nothing
  }

  protected abstract String getVCFileNameSuffix();

  /**
   * 
   * @param <T>
   * @param originalSectName
   * @param type
   * @return
   */
  protected <K> Key<K> createSMKey(String originalSectName, Class<K> type)
  {
    return new Key<K>(originalSectName, type);
  }

  protected void printBenchmarks(int exitCode, long totalNumberErrors, SortedMap<String, List<Long>> timesPerFile)
  {
//     timesPerFile.put(file, Arrays.asList(parsingErrors, typeErrors,
//              vcgErrors, printErrors, parsingTime, typeCheckTime,
//              vcgTime, printTime, typeCheckTime + vcgTime + printTime));
//
    for (Map.Entry<String, List<Long>> entry: timesPerFile.entrySet())
    {
      List<Long> times = entry.getValue();
      System.out.println("\t" + times.get(8) + "ms for " + entry.getKey() + ":");
      System.out.println("\t\tparsing errors.." + times.get(0));
      System.out.println("\t\ttype errors....." + times.get(1));
      System.out.println("\t\tVCG errors......" + times.get(2));
      System.out.print  ("\t\tprint errors...." + times.get(3));
      System.out.println(" (" + totalNumberErrors + " errors in total)");
      System.out.println("\t\tparser.........." + times.get(4) + "ms");
      System.out.println("\t\ttypechecker....." + times.get(5) + "ms");
      System.out.println("\t\tVC generation..." + times.get(6) + "ms");
      System.out.println("\t\tprinter........." + times.get(7) + "ms");
      System.out.println("\n\t\tAST instance...." + BaseFactory.howManyInstancesCreated());
    }
    System.out.println("\t with exit code = " + exitCode);
  }

  protected void writeToFile(CztPrintString output, String vcFileName) throws VCGException
  {
    // write the printed result on to the dc filename
    try
    {
      //FileWriter writer = new FileWriter(vcFileName);
      Writer writer = new OutputStreamWriter(new FileOutputStream(vcFileName), StandardCharsets.UTF_8);
      writer.write(output.toString());
      writer.close();
    }
    catch (IOException e)
    {
      throw new VCGException(getVCG().getManager().getDialect(), "VCGU-PRINT-ERROR = " + vcFileName, e);
    }
  }

  /**
   * Makes sure the given VCEnvAnn is known within the underlying section manager,
   * and that its VC ZSect and original ZSect are also known. It of course, first checks
   * there is a section manager configured.
   * @param zSectVCEnv VC ZSect env to check
   * @throws VCGException if it is inconsistent.
   */
  protected void checkVCZSectConsistency(VCEnvAnn zSectVCEnv) throws VCGException
  {
    assert zSectVCEnv != null;

    final String sectNameVC = zSectVCEnv.getVCSectName();
    final String sectName = zSectVCEnv.getOriginalZSectName();

    // make sure there is a section manager configured
    SectionManager manager = getVCG().config();
    try
    {
      // make sure the manager knows about the VC ZSect and about the original one
      manager.get(new Key<ZSect>(sectName, ZSect.class));
      manager.get(new Key<ZSect>(sectNameVC, ZSect.class));

      // make sure this is indeed a VC ZSect for it: returns zSectVCEnv
      VCEnvAnn there = manager.get(createSMKey(sectName, getVCG().getVCEnvAnnClass()));
      assert there != null;
    }
    catch (CommandException ex)
    {
      final String msg = "VCGU-PRINT-ZSECT-NOT-DOMCHECKED = " + sectNameVC;
      throw new VCGException(ex.getDialect(), msg, ex);
    }
  }

  protected void checkVCFileAndUpdateManager(String vcFileName/*, String vcSectName*/) throws VCGException
  {
    SectionManager manager = getVCG().config();

   // check if new dcFile is okay (e.g., new or can be overwritten)
    File vcFile = new File(vcFileName);
    if (vcFile.exists())
    {
      boolean couldDelete = vcFile.delete();
      final String msg = "VCGU-PRINT-FILEERROR = file already exists; trying to delete "
                         + vcFileName + " = " + couldDelete;
      manager.getLogger().warning(msg);
      if (!couldDelete)
      {
        throw new VCGException(getVCG().getManager().getDialect(), msg);
      }
    }

    // makes ./foo/bar.ext -> bar
    String vcSectName = getSourceName(vcFileName);
    // add the file to be created as a source for the DC ZSect in SectionManager
    Key<Source> vcSource = new Key<Source>(vcSectName, Source.class);
    if (!manager.isCached(vcSource))
    {
      FileSource vcFileSource = new FileSource(vcFile);
      manager.put(vcSource, vcFileSource);
    }
  }

  /* VCG CALCULATION METHODS FOR COMMANDS AND OTHER USES */

  /**
   * Retrieves the ZSect VC Env for the given ZSect. It sets up the
   * domain checker and calls the underlying {@link VCG#createVCEnvAnn(net.sourceforge.czt.z.ast.ZSect)}.
   * This method is useful for Command classes that need to calculate
   * VCs for ZSect to be stored in the section manager.
   * @param zSect Z section to calculate VCs
   * @return ZSect DC environment
   * @throws VCGException if VC calculation throws an exception (e.g., if SectionManager is not set)
   */
  public VCEnvAnn calculateZSectVCEnv(ZSect zSect) throws VCGException
  {
    assert zSect != null;
    getVCG().config();
    VCEnvAnn result = getVCG().createVCEnvAnn(zSect);

    // check consistency between given z section and assigned name within the
    // environment created by the vcs calculator
    assert result != null && result.getOriginalZSectName().equals(zSect.getName());
    return result;
  }

  /**
   * Retrieves the ZSect VC Env for the given Term. It sets up the
   * VC and calls the underlying {@link VCG#createVCEnvAnn(net.sourceforge.czt.base.ast.Term) }.
   * This method is useful for Command classes that need to calculate
   * VCs for ZSect to be stored in the section manager.
   * @param term to calculate VCs
   * @return ZSect DC environment
   * @throws VCGException if DC calculation throws an exception
   */
  public VCEnvAnn calculateVCEnv(Term term) throws VCGException
  {
    assert term != null && !(term instanceof Spec);
    getVCG().config();
    VCEnvAnn result = getVCG().createVCEnvAnn(term);
    return result;
  }

  /**
   * Prints the given VC ZSect environment in the given markup as a CZT string.
   * This can be used by programs that want to process the results of a VC ZSect,
   * like those managing Specs.
   *
   * @param zSectVCEnv
   * @param markup
   * @return
   * @throws VCGException
   */
  public CztPrintString print(VCEnvAnn zSectVCEnv, Markup markup) throws VCGException
  {
    assert zSectVCEnv != null;

    final String sectNameVC = zSectVCEnv.getVCSectName();
    //final String sectName = zSectVCEnv.getOriginalZSectName();

    // check there is indeed both DC ZSect and its original
    checkVCZSectConsistency(zSectVCEnv);

    // ask for the printToFile string for the given ZSect in LATEX, please
    CztPrintString output = null;
    SectionManager manager = getVCG().config();
    try
    {
      // prints it using the right markup printer and add as a StringSource to manager, if source is unknown
      output = PrintUtils.printCztStringOf(sectNameVC, manager, markup);
    }
    catch (CommandException ex)
    {
      final String msg = "VCGU-PRINT-ERROR = " + sectNameVC;
      throw new VCGException(ex.getDialect(), msg, ex);
    }
    assert output != null;
    return output;
  }

  /**
   * Prints the given VC ZSect name as a file in the given path and given Markup.
   * It also checks that the given VCEnvAnn is known to the section manager.
   * This can be used by programs producing a result file from a given ZSect VC.
   *
   * @param zSectVCEnv VCs from ZSection to create file for.
   * @param path path where file is to be created
   * @param markup which markup to printToFile the file into.
   * @throws VCGException if the file exists and cannot be deleted/rewritten or if other Commands (e.g., printing) fails.
   */
  public void printToFile(VCEnvAnn zSectVCEnv, String path, Markup markup) throws VCGException
  {
    assert zSectVCEnv != null && path != null;

    // check weather the dcFileName already exists, deleting it if so.
    // ex: zSectVCEnv=sect_??, path = ./foo  => ./foo/sect_??.tex
    final String sectNameVC = zSectVCEnv.getVCSectName();
    final String vcFileName = path + File.separatorChar
                              + sectNameVC + Markup.getDefaultFileExtention(markup);

    getVCG().config();

    // check there is indeed both DC ZSect and its original
    checkVCZSectConsistency(zSectVCEnv);

    // check if new dcFile is okay (e.g., new or can be overwritten)
    // add the file to be created as a source for the DC ZSect in SectionManager
    checkVCFileAndUpdateManager(vcFileName);

    // prints the output - it will use hte FileSource in the manager
    CztPrintString output = print(zSectVCEnv, markup);

    // write the printed result on to the dc filename
    writeToFile(output, vcFileName);
  }

  /**
   * Calculates the VCG results (see {@link #vcg(java.io.File) }) and
   * writes then to a file according to {@link #getVCFilename(java.lang.String, java.lang.String) }.
   * @param file
   * @throws VCGException
   */
  public void vcgToFile(File file) throws VCGException
  {
    // makes ./foo/bar.ext -> ./foo/bar_dc.ext
    final String vcFileName = getVCFileName(file.getAbsolutePath(), getVCFileNameSuffix());

    // domain check the file and get the overall result
    CztPrintString output = vcg(file);

    // check the file has all the info in the sect manager and that we can create it
    checkVCFileAndUpdateManager(vcFileName);

    // write the printed result on to the dc filename
    writeToFile(output, vcFileName);
  }

  /**
   * Given a file containing one or more ZSects, prints a CZT string corresponding
   * to the section(s) in the file. If there are more than one ZSect, the results
   * are concatenated. The markup is determined by the file extension (see Markup.getMarkup(String)).
   * Since a file should not have more than one markup, the result can be nicely concatenated.
   * This can be used by programs that have a file they want to get the VC results as a String,
   * which can be used to update the section manager for the new Source.
   * @param file
   * @return collected CztPrintString of information from file.
   * @throws VCGException
   */
  public CztPrintString vcg(File file) throws VCGException
  {
    final String fileName = file.getAbsolutePath();
    final String sourceName = getSourceName(fileName);
    try
    {
      SectionManager manager = getVCG().config();
      String localcztpath = manager.getProperty("czt.path");
      if (localcztpath == null || localcztpath.isEmpty())
      {
        localcztpath = file.getParent();
      }
      else
      {
        localcztpath += File.pathSeparator + file.getParent();
      }
      manager.setProperty("czt.path", localcztpath);

      // for parsing, we better fix the source as well for the section manager.
      Key<Source> srcKey = new Key<Source>(sourceName, Source.class);
      if (!manager.isCached(srcKey))
      {
        manager.put(srcKey, new FileSource(file));
      }
      // retrieve the spec
      Spec spec = manager.get(new Key<Spec>(sourceName, Spec.class));
      if (spec == null)
        throw new VCGException(getVCG().getManager().getDialect(), "VCGU-NULL-SPEC-ON-FILE- = " + fileName);

      // process all ZSects to collect resulting CztPrintStrings
      CztPrintString output = null;
      final Markup markup = Markup.getMarkup(fileName);
      StringBuilder result = new StringBuilder("\n");
      for (Sect sect : spec.getSect())
      {
        if (sect instanceof ZSect)
        {
          ZSect zSect = (ZSect) sect;
          VCEnvAnn zSectDCEnvAnn = calculateZSectVCEnv(zSect);
          output = print(zSectDCEnvAnn, markup);
          result.append(output.toString());
          result.append("\n");
        }
      }

      // depending on the Markup create the right final version.
      output = null;
      switch (markup)
      {
        case LATEX:
          output = new LatexString(result.toString(), manager.getDialect());
          break;
        case UNICODE:
          output = new UnicodeString(result.toString(), manager.getDialect());
          break;
        case ZML:
          output = new XmlString(result.toString(), manager.getDialect());
          break;
        default:
          final String msg = "VCGU-PRINT-UNKNOWN-MARKUP = " + markup;
          manager.getLogger().warning(msg);
          throw new VCGException(getVCG().getManager().getDialect(), msg);
      }
      assert output != null;
      return output;
    }
    catch (ParseException f)
    {
      throw new VCGException(f.getDialect(), "VCGU-VC-ZSECT-PARSE-ERROR = " + sourceName, f);
    }
    catch (CommandException g)
    {
      if (!(g instanceof VCGException))
        throw new VCGException(g.getDialect(), "VCGU-VC-ZSECT-CMDEXP = " + sourceName, g);
      else
        throw (VCGException)g;
    }
  }

  /* COMMAND LINE PROCESSING */

  protected void run(String[] args)
  {
    int result = 0;
    byte exitCode = 0;

    if (args.length == 0)
    {
      printUsage();
      //System.exit(0);
      return;
    }
    List<String> files = new java.util.ArrayList<String>();
    boolean printBenchmark = printBenchmarkDefault();
    String cztpath = cztPathDefault();
    setExtension(cztExtensionDefault());
    Markup preferedMarkup = preferedMarkupDefault();

    Boolean raiseWarnings = null;
    Boolean hideWarnings = null;
    Boolean processParents = null;
    Boolean addTrivialVC = null;
    Boolean checkDefTblConsistency = null;
    Boolean applyPredTransf = null;
    SortedSet<String> parentsToIgnore = null;

    for (int i = 0; i < args.length; i++)
    {
      //if ("-a".equals(args[i]))
      //{
      //  useInfixAppliesTo = true;
      //}
      //else
      if (isKnownArg(args[i]))
      {
        processArg(args[i]);
      }
      else if ("-b".equals(args[i]))
      {
        printBenchmark = true;
      }
      else if ("-p".equals(args[i]))
      {
        processParents = true;
      }
      else if ("-t".equals(args[i]))
      {
        addTrivialVC = true;
      }
      else if ("-y".equals(args[i]))
      {
        checkDefTblConsistency = true;
      }
      else if ("-w".equals(args[i]))
      {
        raiseWarnings = true;
      }
      else if ("-h".equals(args[i]))
      {
        // raise has precedence over hide
        if (raiseWarnings == null)
        {
          hideWarnings = true;
        }
      }
      else if ("-s".equals(args[i]))
      {
        // raise has precedence over hide
        if (raiseWarnings == null)
        {
          hideWarnings = false;
        }
      }
      else if ("-r".equals(args[i]))
      {
        applyPredTransf = true;
      }
      else if (args[i].startsWith("-m"))
      {
        final String pm = args[i].substring(2/*"-m".length()*/).toUpperCase();
        try
        {
          preferedMarkup = Markup.valueOf(pm);
        }
        catch (IllegalArgumentException e)
        {
          printUsage();
          System.err.println("Unknown prefered markup " + pm);
          System.exit(-2);
        }
      }
      else if (args[i].startsWith("-e"))
      {
        final String ext = args[i].substring(2).toUpperCase();
        try
        {
          setExtension(Dialect.valueOf(ext));
        }
        catch (IllegalArgumentException e)
        {
          printUsage();
          System.err.println("Unknown CZT extension " + ext);
          System.exit(-3);
        }
      }
      else if ("--debug".equals(args[i]))
      {
        debug_ = true;
      }
      else if (args[i].equals("-i"))
      {
        if (i == args.length)
        {
          printUsage();
          System.err.println("\nYou need to provide an argument for `-i'");
          System.exit(-3);
        }
        i++;
        parentsToIgnore = new TreeSet<String>(
                Arrays.asList(args[i].trim().split(
                  SectionManager.SECTION_MANAGER_LIST_PROPERTY_SEPARATOR)));

      }
      else if (args[i].equals("-cp"))
      {
        if (i == args.length)
        {
          printUsage();
          System.err.println("\nYou need to provide an argument for `-cp'");
          System.exit(-4);
        }
        i++;
        cztpath = args[i].trim();
      }
      // -i not yet implemented!
      else if (args[i].startsWith("-"))
      {
        printUsage();
        System.exit(-5);
      }
      else
      {
        files.add(args[i]);
      }
    }

        // retrieve section manager and update its CZT properties.
    SectionManager manager = null;
    try
    {
      manager = createSectionManager(getExtension());
    }
    catch (VCGException e)
    {
      commandException("VCGU-SM-CREATE", e, getExtension().toString(), debug_);
      System.exit(-1);
    }
    assert manager != null && isConfigured();

    // collect default.
    VCG<//?, 
    	?, ?> vcg = getVCG();


    raiseWarnings = raiseWarnings == null ? vcg.isRaisingTypeWarnings() : raiseWarnings;
    // non-default extensions, hide warnings (e.g., ZEves) if not raising.
    hideWarnings = !raiseWarnings && (hideWarnings == null ? !getExtension().equals(SectionManager.DEFAULT_EXTENSION) : hideWarnings);
    
    processParents = processParents == null ? vcg.isProcessingParents() : processParents;
    addTrivialVC = addTrivialVC == null ? vcg.isAddingTrivialVC() : addTrivialVC;
    checkDefTblConsistency = checkDefTblConsistency == null ? vcg.isCheckingDefTblConsistency() : checkDefTblConsistency;
    applyPredTransf = applyPredTransf == null ? vcg.getVCCollector().getTransformer().isApplyingTransformer() : applyPredTransf;
    parentsToIgnore = parentsToIgnore == null ? vcg.getParentsToIgnore() : parentsToIgnore;

    manager.setProperty(PROP_VCG_PROCESS_PARENTS, String.valueOf(processParents));
    manager.setProperty(PROP_VCG_ADD_TRIVIAL_VC, String.valueOf(addTrivialVC));
    manager.setProperty(PROP_VCG_APPLY_TRANSFORMERS, String.valueOf(applyPredTransf));
    manager.setProperty(PROP_VCG_RAISE_TYPE_WARNINGS, String.valueOf(raiseWarnings));
    manager.setProperty(TypecheckPropertiesKeys.PROP_TYPECHECK_WARNINGS_OUTPUT,
        String.valueOf(raiseWarnings != null && raiseWarnings ? WarningOutput.RAISE : hideWarnings != null && hideWarnings ? WarningOutput.HIDE : WarningOutput.SHOW));

    manager.setProperty(PROP_VCGU_PREFERRED_OUTPUT_MARKUP, preferedMarkup.toString());
    manager.setProperty(PROP_VCG_CHECK_DEFTBL_CONSISTENCY, String.valueOf(checkDefTblConsistency));
    manager.setProperty(LatexPrinterPropertyKeys.PROP_LATEXPRINTER_WRAPPING,
            String.valueOf(latexOutputWrappingDefault()));
    processCollectedProperties();
    //manager.setProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO, String.valueOf(useInfixAppliesTo));

    manager.setTracing(debug_);

    String localcztpath = "";
    if (cztpath != null && !cztpath.trim().isEmpty())
    {
      String oldcztpath = manager.getProperty("czt.path");
      if (oldcztpath != null && !oldcztpath.trim().isEmpty())
      {
        cztpath = oldcztpath + File.pathSeparator + cztpath;
      }
      localcztpath = cztpath;
    }

    //List<String> parentsToIgnoreList = null;
    if (parentsToIgnore != null && !parentsToIgnore.isEmpty())
    {
      // get old property
      String oldpipath = manager.getProperty(PROP_VCG_PARENTS_TO_IGNORE);

      // upsate the old new property
      StringBuilder prop = new StringBuilder();
      if (oldpipath != null && !oldpipath.trim().isEmpty())
      {
        prop.append(oldpipath);
        prop.append(File.pathSeparator);
      }

      // build it from parents to ignore
      for (String path : parentsToIgnore)
      {
        // add any extra ones
        if (prop.indexOf(path) == -1)
            prop.append(path);
            prop.append(File.pathSeparator);
      }
      String propS = prop.toString();
      if (prop.length() > 0 )//!prop.isEmpty())
      {
        propS = prop.substring(0, prop.lastIndexOf(File.pathSeparator));
      }

      // set the value
      manager.setProperty(PROP_VCG_PARENTS_TO_IGNORE, propS);
      //parentsToIgnoreList = manager.getListProperty(parentsToIgnore);
    }

    // configure the section manager
    try
    {
      getVCG().setSectionManager(manager);
    }
    catch (VCGException ex)
    {
      commandException("VCGU-SM-CONFIG-ERROR", ex, cztpath, debug_);
      System.exit(-6);
    }

    SortedMap<String, List<Long>> timesPerFile = new TreeMap<String, List<Long>>();
    long zeroTime = System.currentTimeMillis();
    long currentTime = zeroTime;
    long lastTime = zeroTime;
    for (String file : files)
    {

      // add the file parent to the path as well.
      File archive = new File(file);
      String filePath = ".";
      if (archive.getParent() != null)
      {
        filePath = archive.getParent();
        if (filePath != null && !filePath.isEmpty())
        {
          localcztpath = filePath;
        }
        if (cztpath != null && !cztpath.isEmpty())
        {
          localcztpath = filePath + File.pathSeparator + cztpath;
        }
      }
      if (/*localcztpath != null && */!localcztpath.trim().isEmpty())
      {
        manager.setProperty("czt.path", localcztpath);
      }

      long parsingErrors = 0;
      long typeErrors = 0;
      long vcgErrors = 0;
      long printErrors = 0;
      long parsingTime = 0;
      long typeCheckTime = 0;
      long vcgTime = 0;
      long printTime = 0;
      Spec spec = null;
      // OriginalSectName -> VCEnvAnn
      SortedMap<String, VCEnvAnn> vcs = new TreeMap<String, VCEnvAnn>();
      String specNameNoPath = null;
      try
      {
        // retrieve it as either a ZSect or Spec - expects file name to be section name
        specNameNoPath = removePath(getFileNameNoExt(file));
        spec = manager.get(new Key<Spec>(specNameNoPath, Spec.class));
      }
      catch (CommandException e)
      {
        if (e.getCause() instanceof ParseException)
        {
          parsingErrors += printParseErrors((ParseException)e.getCause());
          exitCode = -10;
        }
        else
        {
          exitCode = -11;
        }
        commandException("parsing", e, "file does not contain Z section " + specNameNoPath, debug_);
      }
      catch (CztException f)
      {
        cztException("parsing", f, specNameNoPath, debug_);
        exitCode = -12;
      }

      /* ex:
       * 0        40
       * |--Parse--|--TypeCheck--|--VC--|--PrintVC--|
       * lt = 0
       * ct = 40
       * pt = 40 (40 - 0)
       */
      lastTime = currentTime;
      currentTime = System.currentTimeMillis();
      parsingTime = currentTime - lastTime;

      // I don't need to do this bit, actually, given the new 
      // VCEnvAnn Command protocol
      boolean wellTyped;
      if (spec != null)
      {
        wellTyped = true;
        for (Sect sect : spec.getSect())
        {
          if (sect instanceof ZSect)
          {
            try
            {
              ZSect zs = (ZSect) sect;
              getVCG().typeCheck(zs.getName(), true);
            }
            catch (CommandException e)
            {
              if (e.getCause() instanceof TypeErrorException)
              {
                typeErrors += printTypeErrors((TypeErrorException)e.getCause());
                exitCode = -21;
              }
              else
              {
                exitCode = -22;
              }
              wellTyped = false;
              commandException("type checking", e, file, debug_);
            }
            catch (CztException f)
            {
              wellTyped = false;
              cztException("type checking", f, file, debug_);
              exitCode = -23;
            }
          }
        }
        
        /* ex:
         * 0        40
         * |--Parse--|--TypeCheck--|--VC--|--PrintVC--|
         * lt = 0
         * ct = 40
         * pt = 40 (40 - 0)
         */
        lastTime = currentTime;
        currentTime = System.currentTimeMillis();
        typeCheckTime = currentTime - lastTime;

        //if the typecheck succeeded, domain check the spec
        //assert spec != null;

        if (wellTyped)
        {
          for (Sect sect : spec.getSect())
          {
            if (sect instanceof ZSect)
            {
              // don't stop upon first failure?
              try
              {

                ZSect zs = (ZSect) sect;
                VCEnvAnn vc = manager.get(createSMKey(zs.getName(), getVCG().getVCEnvAnnClass()));
                VCEnvAnn old = vcs.put(zs.getName(), vc);

                if (old != null)
                  SectionManager.traceWarning("VCGU-DUPLICATE-VCENVANN = " + zs.getName());

                // if processing parents, print them as well
                if (processParents)
                {
                  // recursively process parents
                  processParents(zs, vcs, manager);
                }
              }
              // TODO: please simplify this very nested exception causality, please(!!!)
              catch (CommandException e)
              {
                String extra = file;
                if (e instanceof VCGException)
                {
                  // if VCG during collection, expose possible def tbl errors
                  if (e instanceof VCCollectionException && e.getCause() instanceof VCGException)
                  {
                    if (e.getCause().getCause() instanceof DefinitionException)
                    {
                      vcgErrors += ((DefinitionException)e.getCause().getCause()).totalNumberOfErrors();
                      extra = ((DefinitionException)e.getCause().getCause()).getMessage();
                      exitCode = -30;
                    }
                    else
                    {
                      vcgErrors++;
                      extra = e.getCause().getMessage();
                      exitCode = -31;
                    }
                  }
                  // if VCG during CmdExp try to get parse / type errors
                  else if (e.getCause() instanceof CommandException)
                  {
                    CommandException vcge = (CommandException)e.getCause();
                    if (vcge.getCause() instanceof ParseException)
                    {
                      parsingErrors += printParseErrors((ParseException)vcge.getCause());
                      exitCode = -32;
                    }
                    else if (vcge.getCause() instanceof TypeErrorException)
                    {
                      typeErrors += printTypeErrors((TypeErrorException)vcge.getCause());
                      exitCode = -33;
                    }
                    else
                    {
                      extra = vcge.getMessage();
                      exitCode = -34;
                    }
                    vcgErrors++;
                  }
                  else
                  {
                    vcgErrors++;
                    extra = e.getCause() != null ? e.getCause().getMessage() : e.getMessage();
                    exitCode = -35;
                  }
                }
                else
                {
                  vcgErrors++;
                  extra = e.getCause() != null ? e.getCause().getMessage() : e.getMessage();
                  exitCode = -36;
                }
                commandException(getClass().getSimpleName(), e, extra, debug_);
              }
              catch (CztException f)
              {
                cztException(getClass().getSimpleName(), f, file, debug_);
                vcgErrors++;
                exitCode = -37;
              }
            }
          }

          /* ex:
           * 0        40            100
           * |--Parse--|--TypeCheck--|--VC--|--PrintVC--|
           * lt = 40
           * ct = 100
           * tt = 60  (100-40)
           */
          lastTime = currentTime;
          currentTime = System.currentTimeMillis();
          vcgTime = currentTime - lastTime;

          // printToFile the collected Domain Check VCs
          if (!vcs.isEmpty())
          {
            System.out.println("Printing VC ZSect(s) for " + file);
            for (VCEnvAnn zSectDC : vcs.values())
            {
              try
              {
                printToFile(zSectDC, filePath, preferedMarkup);
              }
              catch (CommandException e)
              {
                commandException("VCGU-PRINT-VC-ZSECT", e, file, debug_);
                printErrors++;
                exitCode = -40;
              }
              catch (CztException f)
              {
                cztException("VCGU-PRINT-VC-ZSECT", f, file, debug_);
                printErrors++;
                exitCode = -41;
              }
            }

            /* ex:
             * 0        40            100
             * |--Parse--|--TypeCheck--|--VC--|--PrintVC--|
             * lt = 40
             * ct = 100
             * tt = 60  (100-40)
             */
            lastTime = currentTime;
            currentTime = System.currentTimeMillis();
            printTime = currentTime - lastTime;
          }
        }
      }
      // result is the number of errors to consider
      result += typeErrors + parsingErrors + vcgErrors + printErrors;
      timesPerFile.put(file, Arrays.asList(parsingErrors, typeErrors,
              vcgErrors, printErrors, parsingTime, typeCheckTime,
              vcgTime, printTime, parsingTime + typeCheckTime + vcgTime + printTime));
      // Reset the currentTime offset
    }
    currentTime = System.currentTimeMillis();
    lastTime = currentTime;
    long totalTime = System.currentTimeMillis() - zeroTime;

    if (printBenchmark)
    {
      System.out.println(totalTime + "ms for " + files.size() + " files.");
      printBenchmarks(exitCode, result, timesPerFile);
    }
    System.exit(exitCode);
  }

  private void processParents(ZSect zs, SortedMap<String, VCEnvAnn> vcs, SectionManager manager) throws CommandException
  {
    for(Parent p : zs.getParent())
    {
      final String pName = p.getWord();
      // if the parent isn't to be ignored and hasn't yet been processed, process it
      if (!getVCG().getParentsToIgnore().contains(pName) && !vcs.containsKey(pName))
      {
        VCEnvAnn vc = manager.get(createSMKey(pName, getVCG().getVCEnvAnnClass()));
        vcs.put(pName, vc);
        ZSect parentZS = manager.get(new Key<ZSect>(pName, ZSect.class));
        processParents(parentZS, vcs, manager);
      }
    }
  }

  /* ERROR HANDLING */

//  public static interface VCGExceptionHandler<E>
//  {
//    public Class<E> getExceptionClass();
//    public int handleException(E e);
//  }
//
//  public static <E extends Throwable> void handleException(E e, String extra, VCGExceptionHandler<E> handler, boolean debug)
//  {
//
//  }
//
//  public static Pair<Integer, Integer> handleExceptionInVCG(Throwable e, String extra, boolean debug)
//  {
//  // TODO: please simplify this very nested exception causality, please(!!!)
//    Integer left = 0;  // number of errors
//    Integer right = 0; // exit code
//    if (e instanceof CommandException)
//    {
//      if (e instanceof VCGException)
//      {
//        // if VCG during collection, expose possible def tbl errors
//        if (e instanceof VCCollectionException && e.getCause() instanceof VCGException)
//        {
//          if (e.getCause().getCause() instanceof DefinitionException)
//          {
//            left  = ((DefinitionException)e.getCause().getCause()).totalNumberOfErrors();
//            extra = ((DefinitionException)e.getCause().getCause()).getMessage() + (extra != null ? "\n" + extra : "");
//            right = -30;
//          }
//          else
//          {
//            left = 1;
//            right = -31;
//          }
//        }
//        // if VCG during CmdExp try to get parse / type errors
//        else if (e.getCause() instanceof CommandException)
//        {
//          CommandException vcge = (CommandException)e.getCause();
//          if (vcge.getCause() instanceof ParseException)
//          {
//            left = printParseErrors((ParseException)vcge.getCause());
//            extra = vcge.getCause().getMessage() + (extra != null ? "\n" + extra : "");
//            right = -32;
//          }
//          else if (vcge.getCause() instanceof TypeErrorException)
//          {
//            left = printTypeErrors((TypeErrorException)vcge.getCause());
//            extra = vcge.getCause().getMessage() + (extra != null ? "\n" + extra : "");
//            right = -33;
//          }
//          else
//          {
//            left = 1;
//            right = -34;
//          }
//        }
//        else
//        {
//          left = 1;
//          right = -35;
//        }
//      }
//      else
//      {
//        left = 1;
//        right = -36;
//      }
//      commandException(e.getClass().getSimpleName(), (CommandException)e, extra, debug);
//    }
//    else if (e instanceof CztException)
//    {
//      cztException(e.getClass().getSimpleName(), (CztException)e, extra, debug);
//      left = 1;
//      right = -37;
//    }
//    return new Pair<Integer, Integer>(left, right);
//  }

  public static int printParseErrors(ParseException pe)
  {
    int result = pe.getErrorList().size();
    pe.printErrorList();
    return result;
  }

  public static int printTypeErrors(TypeErrorException te)
  {
    int result = te.getErrors().size();
    // VCG already prints errors.
    //te.printErrors();
    return result;
  }

  protected static void commandException(String job, CommandException e, String extra, boolean debug)
  {
    System.err.println("Command exception has happened while " + job
                       + "\n\t message = " + e.getMessage()
                       + "\n\t cause   = " + (e.getCause() != null ? e.getCause().getMessage() : "none")
                       + "\n\t clue    = " + extra);
    if (debug)
    {
      e.printStackTrace();
    }
    //System.err.flush();
    //System.exit(-1);
  }

  protected static void cztException(String job, CztException e, String extra, boolean debug)
  {
    System.err.println("CZT exception " + e.getClass().getSimpleName()
                       + " has happened while " + job
                       + "\n\t message = " + e.getMessage()
                       + "\n\t cause   = " + (e.getCause() != null ? e.getCause().getMessage() : "none")
                       + "\n\t clue    = " + extra
                       + "\n\t BUG!    = opps. Please report it to czt-devel@lists.sourceforge.net");
    if (debug)
    {
      e.printStackTrace();
    }
    //System.err.flush();
  }
  
  public static List<? extends Throwable> handleVCGException(VCGException e, String jobName)
  {
    String extra = "";
    int vcgErrors = 0;
    int parsingErrors = 0;
    int typeErrors = 0;
    List<Throwable> result = new ArrayList<Throwable>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    // if VCG during collection, expose possible def tbl errors
    if (e instanceof VCCollectionException && e.getCause() instanceof VCGException)
    {
      if (e.getCause().getCause() instanceof DefinitionException)
      {
        DefinitionException de = ((DefinitionException)e.getCause().getCause());
        vcgErrors += de.totalNumberOfErrors();
        extra = ((DefinitionException)e.getCause().getCause()).getMessage();
        result.add(de);
      }
      else
      {
        vcgErrors++;
        extra = e.getCause().getMessage();
        result.add(e.getCause());
      }
    }
    // if VCG during CmdExp try to get parse / type errors
    else if (e.getCause() instanceof CommandException)
    {
      CommandException vcge = (CommandException)e.getCause();
      if (vcge.getCause() instanceof ParseException)
      {
        ParseException pe = (ParseException)vcge.getCause();
        parsingErrors += pe.getErrors().size();
        result.add(vcge.getCause());
      }
      else if (vcge.getCause() instanceof TypeErrorException)
      {
        TypeErrorException te = (TypeErrorException)vcge.getCause();
        typeErrors += te.getErrors().size();
        result.add(vcge.getCause());
      }
      else
      {
        extra = vcge.getMessage();
        result.add(vcge);
      }
      vcgErrors++;
    }
    else
    {
      vcgErrors++;
      extra = e.getCause() != null ? e.getCause().getMessage() : e.getMessage();
      if (e.getCause() != null)
        result.add(e.getCause());
    }
    RuntimeException rte = new RuntimeException("VCG exception has happened while " + jobName
                       + "\n\t message = " + e.getMessage()
                       + "\n\t cause   = " + (e.getCause() != null ? e.getCause().getMessage() : "none")
                       + "\n\t parser  = " + parsingErrors + " errors"
                       + "\n\t typechk = " + typeErrors + " errors"
                       + "\n\t vcgerr  = " + vcgErrors + " errors"
                       + "\n\t clue    = " + extra);
    result.add(0, rte);
    return result;
  }


  /* UTILITY CLASS STATIC METHODS */

  private static void checkString(String s)
  {
    if (s == null || s.isEmpty())
    {
      throw new IllegalArgumentException("VCGU-STR-NULL-OR-EMPTY");
    }
  }

  /**
   * For a file "./dir/foo.ext", returns "./dir/foosuffix.ext".
   * If .ext is not present, suffix is just added to the end.
   * @param filename full file name to add suffix before .ext
   * @return file name with added suffix before .ext
   */
  public static String getVCFileName(String filename, String suffix)
  {
    checkString(filename);
    checkString(suffix);
    int dotIdx = filename.lastIndexOf('.');
    if (dotIdx == -1)
    {
      return filename + suffix;
    }
    else
    {
      return filename.substring(0, dotIdx)
             + suffix
             + filename.substring(dotIdx);
    }
  }

  /**
   * For a file "./dir/foo.ext" or ".\dir\foo.ext", removes
   * the path such that the result is "foo.ext". If "foo.ext"
   * is given, it is directly returned.
   * @param filename full file name to remove path
   * @return file name with path removed
   */
  public static String removePath(String filename)
  {
    checkString(filename);
    int barIdx = filename.lastIndexOf(File.separatorChar);
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('/');
    }
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('\\');
    }
    return barIdx == -1 ? filename : filename.substring(barIdx + 1);
  }

  /**
   * For a file "./dir/foo.ext" or ".\dir\foo.ext", extracts
   * the path such that the result is "./dir/". If "foo.ext"
   * is given, "./" is returned.
   * @param filename full file name to remove path
   * @return path from file name
   */
  public static String extractPath(String filename)
  {
    checkString(filename);
    int barIdx = filename.lastIndexOf(File.separatorChar);
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('/');
    }
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf('\\');
    }
    return barIdx == -1 ? "./" : filename.substring(0, barIdx);
  }

  /**
   * For a file "./dir/foo.ext", returns "./dir/foo".
   * If no extension is present, the filename given is returned.
   * @param filename full file name to remove extension
   * @return filename without extension
   */
  public static String getFileNameNoExt(String filename)
  {
    checkString(filename);
    int dotIdx = filename.lastIndexOf('.');
    return dotIdx == -1 ? filename : filename.substring(0, dotIdx);
  }

  /**
   * Get the CZT Source name from a given file. It removes the
   * path for the file name without extension.
   *
   * @param filename
   * @return
   */
  public static String getSourceName(String filename)
  {
    // transforms c:\temp\myfile.tex into myfile
    String resource = removePath(getFileNameNoExt(filename));
    return resource;
  }
}
//WATCH!
//printToFile(manager.get(new Key("sectName", net.sourceforge.czt.vcg.z.dc.DCVCEnvAnn.class)), filePath, Markup.LATEX)