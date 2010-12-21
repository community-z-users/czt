/*
  Copyright (C) 2006, 2007 Petra Malik
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

package net.sourceforge.czt.ui;

import java.io.*;
import java.lang.reflect.*;
import java.net.URL;
import java.util.*;
import java.util.logging.*;
import net.sourceforge.czt.dc.z.DomainCheckPropertyKeys;

import net.sourceforge.czt.dc.z.ZSectDCEnvAnn;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.print.util.*;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.prover.ProofTree;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;

/**
 * The command line user interface for CZT.
 */
public class Main
{
  public static final String PREFIX = "java -jar czt.jar ";
  private Level verbosityLevel_ = Level.WARNING;
  private boolean debug_ = false;

  public static void main(String[] args)
    throws Throwable
  {
    if (args == null || args.length == 0) {
      CZTGui gui = new CZTGui();
      gui.go();
    }
    else
    {
      Main main = new Main();
      main.run(args);
    }
  }

  public void run(String[] args)
    throws Throwable
  {
    try {
      parseArgs(args);
    }
    catch (CommandException e) {
      if (e.getCause() != null) {
        if (e.getCause().getMessage() != null &&
            verbosityLevel_.intValue() >= Level.INFO.intValue() ) {
          System.err.println(e.getCause().getMessage());
          return;
        }
        throw e.getCause();
      }
      throw e;
    }
  }

  private String getDCFilename(String filename)
  {    
    int dotIdx = filename.lastIndexOf(".");
    assert dotIdx != -1 : "invalid file name (no .ext): " + filename; 
    String filenameDC = filename.substring(0, dotIdx) + 
            DomainCheckPropertyKeys.DOMAIN_CHECK_GENERAL_NAME_SUFFIX + filename.substring(dotIdx);
    return filenameDC;
  }

  public void parseArgs(String[] args)
    throws Throwable
  {
    if (args.length == 0) {
      System.out.println(usage());
      return;
    }
    if (! args[0].startsWith("-") && ! args[0].contains(".")) {
      command(args);
    }
    else {
      String extension = "z";
      String output = null;
      String cztpath = null;
      boolean syntaxCheckOnly = false;
      boolean prove = false;
      boolean printIds = false;
      boolean isBufferingWanted = false;
      boolean isNarrativeWanted = false;      
      boolean useSpecReader = false; 
      boolean domainCheck = false;
      for (int i = 0; i < args.length; i++) {
        if ("-h".equals(args[i]) ||
            "-help".equals(args[i]) ||
            "--help".equals(args[i])) {
          System.err.println(usage());
          return;
        }
        if ("--debug".equals(args[i]))
        {
          debug_ = true;
        }
        else if("-s".equals(args[i])) {
          syntaxCheckOnly = true;
        }
        else if ("-p".equals(args[i])) {
          prove = true;
          extension = "zpatt";
        }
        else if ("-dc".equals(args[i]))
        {
          domainCheck = true;
        }
        else if ("-v".equals(args[i])) {
          verbosityLevel_ = Level.INFO;
        }
        else if ("-vv".equals(args[i])) {
          verbosityLevel_ = SectionManager.DEFAULT_LOGLEVEL;
        }
        else if ("-id".equals(args[i]) ||
                 "-ids".equals(args[i])) {
          printIds = true;
        }
        else if ("-d".equals(args[i])) {
          if (i + 1 < args.length) {
            extension = args[++i];
          }
          else {
            System.err.println(usage());
            return;
          }
        }
        else if ("-o".equals(args[i])) {
          if (i + 1 < args.length) {
            output = args[++i];
          }
          else {
            System.err.println(usage());
            return;
          }
        }
        else if (args[i].startsWith("-g")) {
          useSpecReader = true;
          isBufferingWanted = args[i].indexOf('b', 2) > -1? true : false;
          isNarrativeWanted = args[i].indexOf('i', 2) > -1? true : false;
        }
        else if (args[i].startsWith("-cp"))
        {           
          if (i == args.length)
          {
            System.err.println(usage());
            System.err.println("\nYou need to provide an argument for `-cp'");
            return;
          }
          i++;
          cztpath = args[i].trim();
        }
        else {
          SectionManager manager = new SectionManager(extension);
          if (debug_)
          {
            manager.setTracingLevel(
               verbosityLevel_.equals(SectionManager.DEFAULT_LOGLEVEL) ?     //    if extra verbosity
                  SectionManager.EXTRA_TRACELEVEL :                          //      extr tracing
                  SectionManager.DEFAULT_TRACELEVEL);                        //    else normal tracing            
          }
          manager.setTracing(debug_);
          // this in case the user has some other console loggers set up.
          // when debugging, always use normal tracing, unless extra verbosity
          // is requested with -vv (e.g., -v is ignored for debugging purposes).
          setConsoleHandlerLoggingLevel(manager.getLogger(),
                  (debug_ ?                                                       // if debugging
                      (verbosityLevel_.equals(SectionManager.DEFAULT_LOGLEVEL) ?  //    if extra verbosity
                          SectionManager.EXTRA_TRACELEVEL :                     //      extra tracing
                          SectionManager.DEFAULT_TRACELEVEL)                        //    else normal tracing
                      : verbosityLevel_));                                        // else normal logging
          //debug(manager, args[i]);          
          if (printIds) {
            manager.setProperty(PrintPropertiesKeys.PROP_PRINT_NAME_IDS,
                                "true");
          }
          Source source = null;
          boolean openOk = false;
          if (useSpecReader)
          {
            for (String suff : net.sourceforge.czt.specreader.SpecReader.SUFFICES) {
              if (args[i].endsWith(suff)) {
                source = new SpecSource(args[i], isBufferingWanted, isNarrativeWanted);
                openOk = true;
                break;
              }
            }
          }
          if (! openOk) {  /* Not latex mark-up, so specreader not used */
            source = new FileSource(args[i]);
          }
          File file = new File(args[i]);                    
          if (file != null && file.getParent() != null) {
            String fileParent = file.getParent();
            String oldcztpath = manager.getProperty("czt.path");
            oldcztpath = (oldcztpath == null ? "" : oldcztpath.trim());
            // if null or empty, just use the parent; otherwise concatenate the 
            // parent at the beginning, since lookup is FIFO ordered.
            cztpath = ((cztpath == null || cztpath.isEmpty()) ? fileParent : 
              (oldcztpath.isEmpty() ? (fileParent + File.pathSeparator + cztpath) :
                (fileParent + File.pathSeparator + oldcztpath + File.pathSeparator + cztpath)));
            if (cztpath != null && !cztpath.trim().isEmpty())
            {
               manager.setProperty("czt.path", cztpath);
            }
          }
          boolean parsed = parse(source, manager, syntaxCheckOnly, prove, domainCheck);
          if (parsed && output != null) {
            String dcOutput = getDCFilename(output);
            if (output.endsWith("8")) {
              UnicodeString unicode = manager.get(
                new Key<UnicodeString>(source.getName(), UnicodeString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream, "UTF-8");
              writer.write(unicode.toString());
              writer.close();
              
              if (domainCheck)
              {
                unicode = manager.get(new Key<UnicodeString>(source.getName() +
                        DomainCheckPropertyKeys.DOMAIN_CHECK_GENERAL_NAME_SUFFIX, UnicodeString.class));
                stream = new FileOutputStream(dcOutput);
                writer = new OutputStreamWriter(stream, "UTF-8");
                writer.write(unicode.toString());
                writer.close();              
              }
            }
            else if (output.endsWith("16")) {
              UnicodeString unicode = manager.get(
                new Key<UnicodeString>(source.getName(), UnicodeString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream, "UTF-16");
              writer.write(unicode.toString());
              writer.close();
              
              if (domainCheck)
              {
                unicode = manager.get(new Key<UnicodeString>(source.getName() +
                        DomainCheckPropertyKeys.DOMAIN_CHECK_GENERAL_NAME_SUFFIX, UnicodeString.class));
                stream = new FileOutputStream(dcOutput);
                writer = new OutputStreamWriter(stream, "UTF-16");
                writer.write(unicode.toString());
                writer.close();               
              }
            }
            else if (output.endsWith("tex") || output.endsWith("zed")) {
              LatexString latex = manager.get(
                new Key<LatexString>(source.getName(), LatexString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream);
              writer.write(latex.toString());
              writer.close();
              
              if (domainCheck)
              {
                latex = manager.get(new Key<LatexString>(source.getName() +
                        DomainCheckPropertyKeys.DOMAIN_CHECK_GENERAL_NAME_SUFFIX, LatexString.class));
                stream = new FileOutputStream(dcOutput);
                writer = new OutputStreamWriter(stream);
                writer.write(latex.toString());
                writer.close(); 
              }
            }
            else if (output.endsWith("xml") || output.endsWith("zml")) {
              XmlString xml = manager.get(
                new Key<XmlString>(source.getName(), XmlString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream, "UTF-8");
              writer.write(xml.toString());
              writer.close();
              
              if (domainCheck)
              {
                xml = manager.get(
                  new Key<XmlString>(source.getName(), XmlString.class));
                stream = new FileOutputStream(dcOutput);
                writer = new OutputStreamWriter(stream, "UTF-8");
                writer.write(xml.toString());
                writer.close();
              }
            }
            else {
              System.err.println("Unsupported output file " + output);
              return;
            }
          }
        }
      }
    }
  }

  /**
   * Returns the version number as a String, or "unknown" if an error
   * occured when accessing the property containing the version
   * information.
   */
  public static String getVersion()
  {
    String version = "unknown";
    try {
      Properties props = new Properties();
      URL url = Main.class.getResource("/net/sourceforge/czt/czt.properties");
      if (url != null) {
        props.load(url.openStream());
        version = (String) props.get("version");
      }
    }
    catch (IOException e) {}
    return version;
  }

  public static String usage()
  {
    return usage(PREFIX);
  }

  public static String usage(String prefix)
  {
    return "Community Z Tools " + getVersion() + "\nUsage:\n" +
      "  " + prefix + "[-d <dialect>] [-g{bi}] [-o <filename>] [-s] <filename>\n" +
      "  " + prefix + "<command> [<commandArg1> .. <commandArgN>]\n" +
      "Flags:\n" +
      "  -d   specify the dialect to be used\n" +
      "  -g   options concerned with gathering of latex mark-up so that\n" +
      "         directives are moved to the beginnings of their sections\n" +
      "     b  buffer whole spec in memory while doing so (faster)\n" +
      "     i  retain informal narrative rather than eliding it\n" +
      "  -o   specify output file (mark-up is determined by file ending)\n" +
      "  -s   syntax check only\n" +
      "  -dc  domain check the specification\n" +
      "  -id  if an output in LaTeX or Unicode mark-up is specified,\n" +
      "       prints the ids for names as part of the name.\n" +
      "       Note that this is for debugging purposes.  The output won't\n" +
      "       typecheck any more.\n" +
      "  -cp <l> specify the value for czt.path as a semicolon-separated list\n"+
      "        of directories (e.g., -cp=./tests;/user/local/pkg/myfiles).\n"+
      "        The list is mandatory and must not be empty.\n"+
      "Dialects:\n" +
      "  z       Standard Z (default)\n" +
      "  oz      Object Z\n" +
      "  circus  Circus language\n" +
      "  zpatt   Z with transformation rules\n" +
      "  ozpatt  Object Z with transformation rules\n" +
      "File ending bindings:\n" +
      "  tex, zed --> LaTeX mark-up\n" +
      "  xml, zml --> ZML\n" +
      "  *8       --> Unicode (encoding UTF-8)\n" +
      "  *16      --> Unicode (encoding UTF-16)\n" +
      "Commands:\n" + printCommands() +
      "\nNOTE: -cp within commands overides the one here.";
  }

  /**
   * The first string contains the command to be invoked,
   * the following are arguments to the command.
   * @param args
   * @throws Throwable
   */
  protected static void command(String[] args)
    throws Throwable
  {
    assert args != null && args.length > 0;
    Properties props = getCommands();
    if (props != null) {
      if (props.keySet().contains(args[0]))
      {
        final String name = props.getProperty(args[0]);
        if (name == null) {
          System.err.println("Cannot find tool " + args[0]);
          System.err.println("Available tools are:\n" + printProperties(props));
          return;
        }
        Class cmdClass = Class.forName(name);
        Method main =
          cmdClass.getMethod("main", new Class[] { args.getClass() });
        try {
          String[] arguments = new String[args.length - 1];
          for (int i = 0; i < arguments.length; i++) {
            arguments[i] = args[i + 1];
          }
          main.invoke(null, new Object[] { arguments });
        }
        catch (InvocationTargetException e) {
          Throwable cause = e.getCause();
          if (cause != null) throw cause;
          throw e;
        }
      }
      else
      {
        System.err.println("Unknown CZT command \'" + args[0] + "\'\n");
        System.err.println(usage());
      }
    }
    else
    {
      throw new RuntimeException("Could not retrieve property file for known commands!");
    }
  }

  public static String printCommands()
  {
    return printProperties(getCommands());
  }

  public static String printProperties(Properties props)
  {
    StringBuilder builder = new StringBuilder();
    for (Map.Entry<Object, Object> entry : props.entrySet()) {
      builder.append("  ").append(entry.getKey()).append(" (bound to ").append(entry.getValue()).append(")\n");
    }
    return builder.toString();
  }

  public static Properties getCommands()
  {
    String errorMessage = "Cannot read resource command.properties";
    try {
      URL url = Main.class.getResource("command.properties");
      Properties result = new Properties();
      InputStream is = url.openStream();
      if (is != null) {
        result.loadFromXML(is);
        return result;
      }
    }
    catch (IOException e) {
      errorMessage += "\n" + e.getMessage();
    }
    System.err.println(errorMessage);
    return null;
  }

  public static boolean parse(Source source,
                              SectionManager manager,
                              boolean syntaxCheckOnly,
                              boolean prove,
                              boolean domainCheck)
    throws CommandException
  {
    Logger logger = CztLogger.getLogger(Main.class);
    logger.info("Parse " + source);
    logger.info("Mark-up is " + source.getMarkup());
    try {
      // set the source for SourceLocator
      String name = source.getName();
      manager.put(new Key<Source>(name, Source.class), source);
      // parse the specification with given name
      Spec spec = manager.get(new Key<Spec>(name, Spec.class));
      int nrOfZSects = 0;
      // for each ZSect within Spec:
      if (spec.getSect().size() > 0) {
        for (Sect sect : spec.getSect()) {
          if (sect instanceof ZSect) {
            ZSect zSect = (ZSect) sect;
            String sectionName = zSect.getName();
            // typecheck it if requested.
            if (! syntaxCheckOnly) {
              manager.get(new Key<SectTypeEnvAnn>(sectionName,
                                  SectTypeEnvAnn.class));
            }
            // domain check it if requested.
            if (domainCheck) {
              manager.get(new Key<ZSectDCEnvAnn>(sectionName,
                                  ZSectDCEnvAnn.class));
            }
            // prove it if requested.
            if (zSect.getParaList() instanceof ZParaList &&
                ((ZParaList) zSect.getParaList()).size() > 0) {
              nrOfZSects++;
              logger.info("Z Section " + sectionName);
              if (prove) {
                RuleTable rules = manager.get(
                  new Key<RuleTable>(sectionName, RuleTable.class));
                if (rules != null) {
                  for (Para p : ((ZParaList) zSect.getParaList())) {
                    if (p instanceof ConjPara) {
                      ConjPara conj = (ConjPara) p;
                      ProofTree.createAndShowGUI(
                        ProverUtils.createSequent(conj.getPred(), true),
                        rules,
                        manager,
                        sectionName);
                    }
                  }
                }
              }
            }
          }
        }
      }
      // check for errors.
      if (nrOfZSects < 1) {
        final String msg = "WARNING: No Z sections found in " + source;
        logger.warning(msg);
        System.err.println(msg);
      }
      try {
        ParseException parseException = manager.get(
          new Key<ParseException>(source.getName(), ParseException.class));
        if (parseException != null) {
          System.out.println(parseException.getErrors().size() +
                             " warnings and errors");
          printErrors(parseException.getErrors());
        }
      }
      catch (CommandException e) {
        // TODO Is ignoring OK?
      }
    }
    catch (CommandException exception) {
      Throwable cause = exception.getCause();
      if (cause instanceof CztErrorList) {
        List<? extends CztError> errors = ((CztErrorList) cause).getErrors();
        printErrors(errors);
        return false;
      }
      else {
        throw exception;
      }
    }
    return true;
  }

  private void setConsoleHandlerLoggingLevel(Logger log, Level level)
  {
    log.setLevel(level);
    Handler[] h = log.getHandlers();
    for (int i = 0; i < h.length; i++) {
      if (h[i] instanceof ConsoleHandler) {
        h[i].setLevel(level);
      }
    }
  }

  private static void printErrors(List<? extends CztError> errors)
  {
    for (CztError error : errors) {
      System.out.println(error);
      if (error.getInfo() != null) {
        System.out.println("  (" + error.getInfo() + ")");
      }
    }
  }


  private void debug(SectionManager manager, String fileName) throws CommandException
  {
    /*
    if (!debug_) return;
    // find the file for it
    //Source source = manager.get(new Key<Source>(fileName, Source.class));
    File f = new File(fileName);
    if (f.exists())
      manager.put(new Key<Source>(fileName, Source.class), new FileSource(f));
    else
      throw new CommandException("Invalid file name " + fileName);
    // parse the specification with given name
    Spec spec = manager.get(new Key<Spec>(fileName, Spec.class));
    for(Sect sect : spec.getSect())
    {
      if (!(sect instanceof ZSect)) continue;
      ZSect zSect = (ZSect) sect;
      String sectionName = zSect.getName();
      // typecheck it
      manager.get(new Key<SectTypeEnvAnn>(sectionName,
                            SectTypeEnvAnn.class));
      // domain check it
      manager.get(new Key<ZSectDCEnvAnn>(sectionName,
                            ZSectDCEnvAnn.class));
    }
    System.exit(0);
     */
  }
}
