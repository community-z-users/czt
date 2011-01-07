/*
Copyright (C) 2004, 2006 Petra Malik
Copyright (C) 2008 Leo Freitas
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
package net.sourceforge.czt.dc.z;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.print.z.LatexPrinterPropertyKeys;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Factory;

/**
 * Utilities for domain checking Z specifications.
 * This class provides a main method for command line use,
 * as well as several 'typecheck' methods that are designed
 * to be called by other Java classes.
 *
 * @author leo
 */
public class DomainCheckUtils implements DomainCheckPropertyKeys
{

  private final DomainChecker domainChecker_;
  // don't use this one, but domainChecker_.getManager()
  private SectionManager sectionManager_ = null;
  private boolean isConfigured_ = false;

  /* CLASS SETUP METHODS */
  /**
   * Do not generate instances of this class.
   * You should use the static methods directly.
   */
  protected DomainCheckUtils()
  {
    domainChecker_ = new DomainChecker();
  }

  protected DomainCheckUtils(Factory factory)
  {
    domainChecker_ = new DomainChecker(factory);
  }

  protected DomainChecker getDC()
  {
    return domainChecker_;
  }

  protected Factory getZFactory()
  {
    return domainChecker_.getZFactory();
  }

  /**
   * This method should be called as few times as possible, as it returns
   * a brand new section manager . It is to be used by the top-level DC application only
   * @param extension the CZT extension to use
   * @return a fresh new section manager. */
  public SectionManager getSectionManager(String extension)
  {
    // if null or for a different dialect, get a new one
    if (sectionManager_ == null || (!sectionManager_.getDialect().equals(extension)))
    {
      setSectionManager(new SectionManager(extension));
    }
    return sectionManager_;
  }

  public void setSectionManager(SectionManager manager)
  {
    if (manager == null) throw new IllegalArgumentException("DCUtils-NULL-SM-GIVEN");
    sectionManager_ = manager;
    sectionManager_.putCommand(ZSectDCEnvAnn.class, DomainCheckUtils.getCommand());
    //sectionManager_.putCommand(SpecDCEnvAnn.class, DomainCheckUtils.getCommand());
    sectionManager_.setProperty(LatexPrinterPropertyKeys.PROP_LATEXPRINTER_WRAPPING, String.valueOf(true));
    resetConfigured();
  }

  protected void resetConfigured()
  {
    isConfigured_ = false;
  }

  protected boolean isConfigured()
  {
    return isConfigured_;
  }

  /**
   * Configures the underlying domain checker to take the section manager properties into account.
   * Should be called by the top-level method only. If the section manager changes, the configuration
   * gets automatically reset. But if properties are changed manually (e.g., properties set), this
   * needs to be updated.
   * @return the DomainChecker SectionManager
   * @throws DomainCheckException
   */
  protected SectionManager config() throws DomainCheckException
  {
    if (!isConfigured())
    {
      if (sectionManager_ == null)
      {
        throw new DomainCheckException("DC-ERROR-NULL-SM");
      }
      domainChecker_.setSectInfo(sectionManager_); // configs the domain checker
      assert domainChecker_.getManager() != null;
      isConfigured_ = true;
    }
    return domainChecker_.getManager();
  }

  /* DOMAIN CHECK CALCULATION METHODS FOR COMMANDS AND OTHER USES */
  /** 
   * Retrieves the ZSect DC Env for the given ZSect. It sets up the
   * domain checker and calls the underlying {@link #DomainChecker.createZSectDCEnvAnn(ZSect)}.
   * This method is useful for Command classes that need to calculate 
   * domain checks for ZSect to be stored in the section manager.
   * @param zSect Z section to calculate domain checks
   * @return ZSect DC environment
   * @throws DomainCheckException if DC calculation throws an exception (e.g., if SectionManager is not set)
   */
  public ZSectDCEnvAnn calculateZSectDCEnv(ZSect zSect)
          throws DomainCheckException
  {
    assert zSect != null;
    config();
    ZSectDCEnvAnn result = domainChecker_.createZSectDCEnvAnn(zSect);
    // check consistency between given z section and assigned name within the 
    // environment created by the domain checker calculator
    assert result != null && result.getOriginalZSectName().equals(zSect.getName());
    return result;
  }

  /**
   * Retrieves the ZSect DC Env for the given Term. It sets up the
   * domain checker and calls the underlying {@link #DomainChecker.createZSectDCEnvAnn(Term)}.
   * This method is useful for Command classes that need to calculate
   * domain checks for ZSect to be stored in the section manager.
   * @param term to calculate domain checks
   * @return ZSect DC environment
   * @throws DomainCheckException if DC calculation throws an exception
   */
  public ZSectDCEnvAnn calculateTermDCEnv(Term term)
          throws DomainCheckException
  {
    assert term != null && !(term instanceof Spec);
    config();
    ZSectDCEnvAnn result = domainChecker_.createZSectDCEnvAnn(term);
    return result;
  }

  /**
   * Makes sure the given ZSectDCEnvAnn is known within the underlying section manager,
   * and that its DC ZSect and original ZSect are also known. It of course, first checks
   * there is a section manager configured.
   * @param zSectDCEnv DC ZSect env to check
   * @throws DomainCheckException if it is inconsistent.
   */
  private void checkDCZSectConsistency(ZSectDCEnvAnn zSectDCEnv) throws DomainCheckException
  {
    assert zSectDCEnv != null;

    final String sectNameDC = zSectDCEnv.getDCZSectName();
    final String sectName = zSectDCEnv.getOriginalZSectName();

    // make sure there is a section manager configured
    SectionManager manager = config();
    try
    {
      // make sure the manager knows about the DC ZSect and about the original one
      manager.get(new Key<ZSect>(sectName, ZSect.class));
      manager.get(new Key<ZSect>(sectNameDC, ZSect.class));

      // make sure this is indeed a DC ZSect for it: returns zSectDCEnv
      ZSectDCEnvAnn there = manager.get(new Key<ZSectDCEnvAnn>(sectName, ZSectDCEnvAnn.class));
      assert there != null;
    }
    catch (CommandException ex)
    {
      final String msg = "DCUtils-PRINT-ZSECT-NOT-DOMCHECKED = " + sectNameDC;
      throw new DomainCheckException(msg, ex);
    }
  }

  private void checkDCFileAndUpdateManager(String dcFileName/*, String dcSectName*/) throws DomainCheckException
  {
    SectionManager manager = config();

   // check if new dcFile is okay (e.g., new or can be overwritten)
    File dcFile = new File(dcFileName);
    if (dcFile.exists())
    {
      boolean couldDelete = dcFile.delete();
      if (!couldDelete)
      {
        final String msg = "DCUtils-PRINT-FILE-WARNING = file already exists; trying to delete "
                            + dcFileName + " = " + couldDelete;
        manager.getLogger().warning(msg);
        throw new DomainCheckException(msg);
      }
    }

    // makes ./foo/bar.ext -> bar
    String dcSectName = getSourceName(dcFileName);
    // add the file to be created as a source for the DC ZSect in SectionManager
    Key<Source> dcSource = new Key<Source>(dcSectName, Source.class);
    if (!manager.isCached(dcSource))
    {
      FileSource dcFileSource = new FileSource(dcFile);
      manager.put(dcSource, dcFileSource);
    }
  }

  /**
   * Prints the given DC ZSect environment in the given markup as a CZT string.
   * This can be used by programs that want to process the results of a DC ZSect,
   * like those managing Specs.
   *
   * @param zSectDCEnv
   * @param markup
   * @return
   * @throws DomainCheckException
   */
  public CztPrintString print(ZSectDCEnvAnn zSectDCEnv, Markup markup) throws DomainCheckException
  {
    assert zSectDCEnv != null;
    
    final String sectNameDC = zSectDCEnv.getDCZSectName();
    final String sectName = zSectDCEnv.getOriginalZSectName();

    // check there is indeed both DC ZSect and its original
    checkDCZSectConsistency(zSectDCEnv);

    // ask for the printToFile string for the given ZSect in LATEX, please
    CztPrintString output = null;
    SectionManager manager = config();
    try
    {
      // prints it using the right markup printer and add as a StringSource to manager, if source is unknown
      output = PrintUtils.printCztStringOf(sectNameDC, manager, markup);
    }
    catch (CommandException ex)
    {
      final String msg = "DCUtils-PRINT-ERROR = " + sectNameDC;
      throw new DomainCheckException(msg, ex);
    }
    assert output != null;
    return output;
  }

  /**
   * Prints the given DC ZSect name as a file in the given path and given Markup.
   * It also checks that the given ZSectDCEnvAnn is known to the section manager.
   * This can be used by programs producing a result file from a given ZSect DC.
   * 
   * @param zSectDCEnv domain checks from ZSection to create file for.
   * @param path path where file is to be created 
   * @param markup which markup to printToFile the file into.
   * @throws DomainCheckException if the file exists and cannot be deleted/rewritten or if other Commands (e.g., printing) fails.
   */
  public void printToFile(ZSectDCEnvAnn zSectDCEnv, String path, Markup markup) throws DomainCheckException
  {
    assert zSectDCEnv != null && path != null;

    // check weather the dcFileName already exists, deleting it if so.
    // ex: zSectDCEnv=sect_dc, path = ./foo  => ./foo/sect_dc.tex
    final String sectNameDC = zSectDCEnv.getDCZSectName();
    final String sectName = zSectDCEnv.getOriginalZSectName();
    final String dcFileName = path + File.separatorChar
                              + sectNameDC + Markup.getDefaultFileExtention(markup);

    SectionManager manager = config();

    // check there is indeed both DC ZSect and its original
    checkDCZSectConsistency(zSectDCEnv);
    
    // check if new dcFile is okay (e.g., new or can be overwritten)
    // add the file to be created as a source for the DC ZSect in SectionManager
    checkDCFileAndUpdateManager(dcFileName);

    // prints the output - it will use hte FileSource in the manager
    CztPrintString output = print(zSectDCEnv, markup);

    // write the printed result on to the dc filename
    try
    {
      FileWriter writer = new FileWriter(dcFileName);
      writer.write(output.toString());
      writer.close();
    }
    catch (IOException e)
    {
      throw new DomainCheckException("DCUtils-PRINT-ERROR = " + dcFileName, e);
    }
  }

  public void domainCheckToFile(File file) throws DomainCheckException
  {
    // makes ./foo/bar.ext -> ./foo/bar_dc.ext
    final String dcFileName = getDCFilename(file.getAbsolutePath());

    // get / config sect manager
    SectionManager manager = config();

    // domain check the file and get the overall result
    CztPrintString output = domainCheck(file);

    // check the file has all the info in the sect manager and that we can create it
    checkDCFileAndUpdateManager(dcFileName);

    // write the printed result on to the dc filename
    try
    {
      FileWriter writer = new FileWriter(dcFileName);
      writer.write(output.toString());
      writer.close();
    }
    catch (IOException e)
    {
      throw new DomainCheckException("DCUtils-PRINT-ERROR = " + dcFileName, e);
    }
  }

  /**
   * Given a file containing one or more ZSects, prints a CZT string corresponding
   * to the section(s) in the file. If there are more than one ZSect, the results
   * are concatenated. The markup is determined by the file extension (see Markup.getMarkup(String)).
   * Since a file should not have more than one markup, the result can be nicely concatenated.
   * This can be used by programs that have a file they want to get the DC results as a String,
   * which can be used to update the section manager for the new Source.
   * @param file 
   * @return collected CztPrintString of information from file.
   * @throws DomainCheckException
   */
  public CztPrintString domainCheck(File file) throws DomainCheckException
  {
    final String fileName = file.getAbsolutePath();
    final String sourceName = getSourceName(fileName);
    try
    {
      SectionManager manager = config();
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
        throw new DomainCheckException("DCUtils-DCNULL-FILE- = " + fileName);

      // process all ZSects to collect resulting CztPrintStrings
      CztPrintString output = null;
      final Markup markup = Markup.getMarkup(fileName);
      StringBuilder result = new StringBuilder("\n");
      for (Sect sect : spec.getSect())
      {
        if (sect instanceof ZSect)
        {
          ZSect zSect = (ZSect) sect;
          ZSectDCEnvAnn zSectDCEnvAnn = calculateZSectDCEnv(zSect);
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
          final String msg = "DCUtils-PRINT-UNKNOWN-MARKUP = " + markup;
          manager.getLogger().warning(msg);
          throw new DomainCheckException(msg);
      }
      assert output != null;
      return output;
    }
    catch (ParseException f)
    {
      throw new DomainCheckException("DCUtils-DC-PARSE-ERROR = " + sourceName, f);
    }
    catch (CommandException g)
    {
      if (!(g instanceof DomainCheckException))
        throw new DomainCheckException("DCUtils-DC-CMDEXP = " + sourceName, g);
      else
        throw (DomainCheckException)g;
    } 
  }

  //  /**
//   * Retrieves the Spec DC Env for the given term. It sets up the domain checker
//   * and calls the underlying {@link #DomainChecker.createSpecDCEnvAnn(Spec)}.
//   * This method is useful for Command classes that need to calculate
//   * domain checks for Spec to be stored in the section manager.
//   * @param term Z specification to calculate domain checks
//   * @return Spec DC environment
//   * @throws DomainCheckException if DC calculation throws an exception
//   */
//  protected SpecDCEnvAnn calculateSpecDCEnv(Spec term)
//    throws DomainCheckException
//  {
//    assert term != null && domainChecker_.getManager() != null;
//    SpecDCEnvAnn result = domainChecker_.createSpecDCEnvAnn(term);
//    return result;
//  }

  /* TOP-LEVEL UTILITY CLASS METHODS */
  protected String name()
  {
    return "zeddomaincheck";
  }

  /** Print a usage message to System.err, describing the
   *  command line arguments accepted by main.
   */
  protected void printUsage()
  {
    System.err.println("usage: " + name() + " [-aptr] filename ...");
    System.err.println("flags: -a     use infix applies to definition.");
    System.err.println("       -b     print execution benchmarks.");
    System.err.println("       -p     process parent sections.");
    System.err.println("       -t     add trivial DC predicates.");
    System.err.println("       -r     apply predicate transformers.");
    System.err.println("       -w     raise type warnings as errors.");
    System.err.println("       -mX    prefered markup to print results");
    System.err.println("              where X=LATEX, UNICODE, XML");
    System.err.println("       -i <l> list of parents to ignore.");
    System.err.println("              a path-separated list of section names");
    System.err.println("              (e.g., -cp ./tests" + File.pathSeparator + "/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");
    System.err.println("      -cp <l> specify the value for czt.path as");
    System.err.println("              a semicolon-separated list of dirs");
    System.err.println("              (e.g., -cp ./tests" + File.pathSeparator + "/user/myfiles).");
    System.err.println("              The list is mandatory and must not be empty.");
    System.err.println("\n");
    System.err.println("Default flags are: \""
                       + ((useInfixAppliesToDefault() ? "-a " : "")
                          + (printBenchmarkDefault() ? "-b " : "")
                          + (processParentsDefault() ? "-p " : "")
                          + (addTrivialDCDefault() ? "-t " : "")
                          + (applyPredTransfDefault() ? "-r " : "")
                          + (raiseWarningsAsErrorsDefault() ? "-w" : "")
                          + ("-m" + preferedMarkupDefault())).trim() + "\"");
  }

  protected boolean printBenchmarkDefault()
  {
    return true;
  }

  protected boolean raiseWarningsAsErrorsDefault()
  {
    return false;
  }

  protected boolean useInfixAppliesToDefault()
  {
    return PROP_DOMAINCHECK_USE_INFIX_APPLIESTO_DEFAULT;
  }

  protected boolean processParentsDefault()
  {
    return PROP_DOMAINCHECK_PROCESS_PARENTS_DEFAULT;
  }

  protected boolean addTrivialDCDefault()
  {
    return PROP_DOMAINCHECK_ADD_TRIVIAL_DC_DEFAULT;
  }

  protected boolean applyPredTransfDefault()
  {
    return PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS_DEFAULT;
  }

  protected String cztPathDefault()
  {
    return null;
  }

  protected String parentToIgnoreListDefault()
  {
    return PROP_DOMAINCHECK_PARENTS_TO_IGNORE_DEFAULT;
  }

  protected Markup preferedMarkupDefault()
  {
    return PROP_DOMAINCHECK_PREFERED_MARKUP_DEFAULT;
  }

  protected String getExtension()
  {
    return SectionManager.DEFAULT_EXTENSION;
  }

  private void commandException(String job, boolean debug, CommandException e, String extra)
  {
    System.err.println("Command exception has happened while " + job
                       + "\n\t message = " + e.getMessage()
                       + "\n\t cause   = " + (e.getCause() != null ? e.getCause().getMessage() : "none")
                       + "\n\t clue    = " + extra);
    if (debug)
    {
      e.printStackTrace();
    }
    //System.exit(-1);
  }

  private void cztException(String job, boolean debug, CztException e, String extra)
  {
    System.err.println("CZT exception " + e.getClass().getSimpleName()
                       + "has happened while " + job
                       + "\n\t message = " + e.getMessage()
                       + "\n\t cause   = " + (e.getCause() != null ? e.getCause().getMessage() : "none")
                       + "\n\t clue    = " + extra
                       + "\n\t BUG!    = opps. Please report it to czt-devel@lists.sourceforge.net");
    if (debug)
    {
      e.printStackTrace();
    }
    //System.exit(-1);
  }

  /* TOP-LEVEL METHODS FOR STANT-ALONE EXECUTION */
  protected void run(String[] args)
  {
    int result = 0;
    byte exitCode = 0;

    if (args.length == 0)
    {
      printUsage();
      System.exit(-1);
    }

    List<String> files = new java.util.ArrayList<String>();
    boolean printBenchmark = printBenchmarkDefault();
    boolean raiseWarnings = raiseWarningsAsErrorsDefault();
    boolean useInfixAppliesTo = useInfixAppliesToDefault();
    boolean processParents = processParentsDefault();
    boolean addTrivialDC = addTrivialDCDefault();
    boolean applyPredTransf = applyPredTransfDefault();
    boolean debug = false;
    String cztpath = cztPathDefault();
    Markup preferedMarkup = preferedMarkupDefault();
    String parentsToIgnore = parentToIgnoreListDefault();
    for (int i = 0; i < args.length; i++)
    {
      if ("-a".equals(args[i]))
      {
        useInfixAppliesTo = true;
      }
      else if ("-b".equals(args[i]))
      {
        printBenchmark = true;
      }
      else if ("-p".equals(args[i]))
      {
        processParents = true;
      }
      else if ("-w".equals(args[i]))
      {
        raiseWarnings = true;
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
      else if ("--debug".equals(args[i]))
      {
        debug = true;
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
        parentsToIgnore = args[i].trim();
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
    SectionManager manager = getSectionManager(getExtension());
    manager.setProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO, String.valueOf(useInfixAppliesTo));
    manager.setProperty(PROP_DOMAINCHECK_PROCESS_PARENTS, String.valueOf(processParents));
    manager.setProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC, String.valueOf(addTrivialDC));
    manager.setProperty(PROP_DOMAINCHECK_APPLY_PRED_TRANSFORMERS, String.valueOf(applyPredTransf));
    manager.setProperty(PROP_DOMAINCHECK_RAISE_TYPE_WARNINGS, String.valueOf(raiseWarnings));
    manager.setProperty(PROP_DOMAINCHECK_PREFERED_MARKUP, preferedMarkup.toString());
    manager.setProperty(LatexPrinterPropertyKeys.PROP_LATEXPRINTER_WRAPPING, String.valueOf(true));
    manager.setTracing(debug);

    // add a potentially old czt path (? TODO: decide to add this or not ?)
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
      String oldpipath = manager.getProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE);
      if (oldpipath != null && !oldpipath.trim().isEmpty())
      {
        parentsToIgnore = oldpipath + File.pathSeparator + parentsToIgnore;
      }
      manager.setProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE, parentsToIgnore);
      //parentsToIgnoreList = manager.getListProperty(parentsToIgnore);
    }
    try
    {
      config();
    }
    catch (DomainCheckException ex)
    {
      System.err.println("DCUtils-SM-CONFIG-ERROR");
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
      if (archive != null && archive.getParent() != null)
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
      if (localcztpath != null && !localcztpath.trim().isEmpty())
      {
        manager.setProperty("czt.path", localcztpath);
      }

      long parsingErrors = 0;
      long typeErrors = 0;
      long parsingTime = 0;
      long typeCheckTime = 0;
      long domainCheckTime = 0;
      long printTime = 0;
      Spec spec = null;
      List<SectTypeEnvAnn> types = new ArrayList<SectTypeEnvAnn>();
      List<ZSectDCEnvAnn> dcVCs = new ArrayList<ZSectDCEnvAnn>();
      String specNameNoPath = null;
      try
      {
        // retrieve it as either a ZSect or Spec - expects file name to be section name
        specNameNoPath = removePath(getFileNameNoExt(file));
        spec = manager.get(new Key<Spec>(specNameNoPath, Spec.class));
      }
      catch (ParseException exception)
      {
        parsingErrors = exception.getErrorList().size();
        exception.printErrorList();
        exitCode = -10;
      }
      catch (CommandException e)
      {
        commandException("parsing", debug, e, "file does not contain Z section " + specNameNoPath);
        exitCode = -11;
      }
      catch (CztException f)
      {
        cztException("parsing", debug, f, specNameNoPath);
        exitCode = -12;
      }
      /* ex:
       * 0        40
       * |--Parse--|--TypeCheck--|--DomainCheck--|--PrintDC--|
       * lt = 0
       * ct = 40
       * pt = 40 (40 - 0)
       */
      lastTime = currentTime;
      currentTime = System.currentTimeMillis();
      parsingTime = currentTime - lastTime;

      // I don't need to do this bit, actually, given the new ZSectDCEnvAnn Command protocol TODO: simplify
      // typecheck + domain cehck each section
      if (spec != null)
      {
        try
        {
          for (Sect sect : spec.getSect())
          {
            if (sect instanceof ZSect)
            {
              ZSect zs = (ZSect) sect;
              SectTypeEnvAnn tp = manager.get(new Key<SectTypeEnvAnn>(zs.getName(), SectTypeEnvAnn.class));
              types.add(tp);
            }
          }
        }
        catch (CommandException e)
        {
          if (e.getCause() != null && e.getCause() instanceof TypeErrorException)
          {
            TypeErrorException te = (TypeErrorException) e.getCause();
            typeErrors = domainChecker_.printErrors(te.errors());
            exitCode = -20;
          }
          else
          {
            commandException("type checking", debug, e, file);
            exitCode = -21;
          }
        }
        catch (CztException f)
        {
          cztException("type checking", debug, f, file);
          exitCode = -22;
        }
        /* ex:
         * 0        40
         * |--Parse--|--TypeCheck--|--DomainCheck--|--PrintDC--|
         * lt = 0
         * ct = 40
         * pt = 40 (40 - 0)
         */
        lastTime = currentTime;
        currentTime = System.currentTimeMillis();
        typeCheckTime = currentTime - lastTime;

        //if the typecheck succeeded, domain check the spec
        assert spec != null;

        if (!types.isEmpty())
        {
          try
          {
            for (Sect sect : spec.getSect())
            {
              if (sect instanceof ZSect)
              {
                ZSect zs = (ZSect) sect;
                ZSectDCEnvAnn dc = manager.get(new Key<ZSectDCEnvAnn>(zs.getName(), ZSectDCEnvAnn.class));
                dcVCs.add(dc);
              }
            }
          }
          catch (CommandException e)
          {
            commandException("domain checking", debug, e, file);
            exitCode = -30;
          }
          catch (CztException f)
          {
            cztException("domain checking", debug, f, file);
            exitCode = -31;
          }

          // result is the number of errors to consider
          result += typeErrors + parsingErrors;

          /* ex:
           * 0        40            100
           * |--Parse--|--TypeCheck--|--DomainCheck--|--PrintType--|
           * lt = 40
           * ct = 100
           * tt = 60  (100-40)
           */
          lastTime = currentTime;
          currentTime = System.currentTimeMillis();
          domainCheckTime = currentTime - lastTime;

          // printToFile the collected Domain Check VCs
          if (!dcVCs.isEmpty())
          {
            try
            {
              System.out.println("Printing DC ZSect(s) for " + file);
              for (ZSectDCEnvAnn zSectDC : dcVCs)
              {
                printToFile(zSectDC, filePath, preferedMarkup);
              }
            }
            catch (CommandException e)
            {
              commandException("printing DC ZSect", debug, e, file);
              exitCode = -40;
            }
            catch (CztException f)
            {
              cztException("printing DC ZSect", debug, f, file);
              exitCode = -41;
            }

            /* ex:
             * 0        40            100
             * |--Parse--|--TypeCheck--|--DomainCheck--|--Print--|
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
      timesPerFile.put(file, Arrays.asList(parsingErrors, typeErrors,
              parsingTime, typeCheckTime, domainCheckTime, printTime, typeCheckTime + domainCheckTime + printTime));
      // Reset the currentTime offset
    }
    currentTime = System.currentTimeMillis();
    lastTime = currentTime;
    long totalTime = System.currentTimeMillis() - zeroTime;

    if (printBenchmark)
    {
      System.out.println(totalTime + "ms for " + files.size() + " files.");
      for (String file : timesPerFile.keySet())
      {
        List<Long> times = timesPerFile.get(file);
        System.out.println("\t" + times.get(6) + "ms for " + file + ":");
        System.out.println("\t\tparsing errors.." + times.get(0));
        System.out.println("\t\ttype errors....." + times.get(1));
        System.out.println("\t\tparser.........." + times.get(2) + "ms");
        System.out.println("\t\ttypechecker....." + times.get(3) + "ms");
        System.out.println("\t\tdomainchecker..." + times.get(4) + "ms");
        System.out.println("\t\tprinter........." + times.get(5) + "ms");
      }
    }
    System.exit(exitCode);
  }

  /* UTILITY CLASS STATIC METHODS */
  private static final DomainCheckUtils domainCheckUtils_ = new DomainCheckUtils();

  public static final DomainCheckUtils getDCUtils()
  {
    return domainCheckUtils_;
  }

  /** 
   * For a file "./dir/foo.ext", returns "./dir/foo_dc.ext".   
   * If .ext is not present, _dc is just added to the end.
   * @param filename full file name to add _dc before .ext
   * @return file name with added _dc before .ext
   */
  public static String getDCFilename(String filename)
  {
    int dotIdx = filename.lastIndexOf(".");
    if (dotIdx == -1)
    {
      return filename + DOMAIN_CHECK_GENERAL_NAME_SUFFIX;
    }
    else
    {
      return filename.substring(0, dotIdx)
             + DOMAIN_CHECK_GENERAL_NAME_SUFFIX
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
    int barIdx = filename.lastIndexOf(File.separatorChar);
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf("/");
    }
    if (barIdx == -1)
    {
      barIdx = filename.lastIndexOf("\\");
    }
    return barIdx == -1 ? filename : filename.substring(barIdx + 1);
  }

  /**
   * For a file "./dir/foo.ext", returns "./dir/foo".
   * If no extension is present, the filename given is returned.
   * @param filename full file name to remove extension
   * @return filename without extension
   */
  public static String getFileNameNoExt(String filename)
  {
    int dotIdx = filename.lastIndexOf(".");
    return dotIdx == -1 ? filename : filename.substring(0, dotIdx);
  }

  /**
   * Get the CZT Source name from a given file.
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

  public static void main(String[] args)
  {
    getDCUtils().run(args);
  }

  /**
   * Get a Command object for use in SectionManager
   *
   * @return A command for typechecking sections.
   */
  public static Command getCommand()
  {
    return new DomainCheckerCommand();
  }
}
