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

  public static void main(String[] args)
    throws Throwable
  {
    if (args == null || args.length == 0) {
      CZTGui gui = new CZTGui();
      gui.go();
    }
    else {
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
      boolean syntaxCheckOnly = false;
      boolean prove = false;
      boolean printIds = false;
      Level level = Level.WARNING;
      for (int i = 0; i < args.length; i++) {
        if ("-h".equals(args[i]) ||
            "-help".equals(args[i]) ||
            "--help".equals(args[i])) {
          System.err.println(usage());
          return;
        }
        if ("-s".equals(args[i])) {
          syntaxCheckOnly = true;
        }
        else if ("-p".equals(args[i])) {
          prove = true;
          extension = "zpatt";
        }
        else if ("-v".equals(args[i])) {
          verbosityLevel_ = Level.INFO;
        }
        else if ("-vv".equals(args[i])) {
          verbosityLevel_ = Level.CONFIG;
          Logger.getLogger("").setLevel(verbosityLevel_);
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
        else {
          setConsoleLogger(verbosityLevel_);
          SectionManager manager = new SectionManager(extension);
          if (printIds) {
            manager.setProperty(PrintPropertiesKeys.PROP_PRINT_NAME_IDS,
                                "true");
          }
          FileSource source = new FileSource(args[i]);
	  File file = new File(args[i]);
	  if (file != null && file.getParent() != null) {
	    manager.setProperty("czt.path", file.getParent());
	  }
          if (parse(source, manager, syntaxCheckOnly, prove) &&
              output != null) {
            if (output.endsWith("8")) {
              UnicodeString unicode = (UnicodeString)
                manager.get(new Key(source.getName(), UnicodeString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream, "UTF-8");
              writer.write(unicode.toString());
              writer.close();
            }
            else if (output.endsWith("16")) {
              UnicodeString unicode = (UnicodeString)
                manager.get(new Key(source.getName(), UnicodeString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream, "UTF-16");
              writer.write(unicode.toString());
              writer.close();
            }
            else if (output.endsWith("tex") || output.endsWith("zed")) {
              LatexString latex = (LatexString)
                manager.get(new Key(source.getName(), LatexString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream);
              writer.write(latex.toString());
              writer.close();
            }
            else if (output.endsWith("xml") || output.endsWith("zml")) {
              XmlString xml = (XmlString)
                manager.get(new Key(source.getName(), XmlString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream, "UTF-8");
              writer.write(xml.toString());
              writer.close();
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
      "  " + prefix + "[-d <dialect>] [-o <filename>] [-s] <filename>\n" +
      "  " + prefix + "<command> [<commandArg1> .. <commandArgN>]\n" +
      "Flags:\n" +
      "  -d   specify the dialect to be used\n" +
      "  -o   specify output file (mark-up is determined by file ending)\n" +
      "  -s   syntax check only\n" +
      "  -id  if an output in LaTeX or Unicode mark-up is specified,\n" +
      "       prints the ids for names as part of the name.\n" +
      "       Note that this is for debugging purposes.  The output won't\n" +
      "       typecheck any more.\n" +
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
      "Commands:\n" + printCommands();
  }

  /**
   * The first string contains the command to be invoked,
   * the following are arguments to the command.
   */
  public static void command(String[] args)
    throws Throwable
  {
    Properties props = getCommands();
    if (props != null) {
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
  }

  public static String printCommands()
  {
    return printProperties(getCommands());
  }

  public static String printProperties(Properties props)
  {
    StringBuilder builder = new StringBuilder();
    for (Map.Entry entry : props.entrySet()) {
      builder.append("  " + entry.getKey() +
                     " (bound to " + entry.getValue() + ")\n");
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
                              boolean prove)
    throws CommandException
  {
    Logger logger = CztLogger.getLogger(Main.class);
    logger.info("Parse " + source);
    logger.info("Mark-up is " + source.getMarkup());
    try {
      String name = source.getName();
      manager.put(new Key(name, Source.class), source);
      Spec spec = (Spec) manager.get(new Key(name, Spec.class));
      int nrOfZSects = 0;
      if (spec.getSect().size() > 0) {
        for (Sect sect : spec.getSect()) {
          if (sect instanceof ZSect) {
            ZSect zSect = (ZSect) sect;
            String sectionName = zSect.getName();
            if (! syntaxCheckOnly) {
              manager.get(new Key(sectionName,
                                  SectTypeEnvAnn.class));
            }
            if (zSect.getParaList() instanceof ZParaList &&
                ((ZParaList) zSect.getParaList()).size() > 0) {
              nrOfZSects++;
              logger.info("Z Section " + sectionName);
              if (prove) {
                RuleTable rules = (RuleTable)
                  manager.get(new Key(sectionName, RuleTable.class));
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
      if (nrOfZSects < 1) {
        System.err.println("WARNING: No Z sections found in " + source);
      }
      try {
        ParseException parseException = (ParseException)
          manager.get(new Key(source.getName(), ParseException.class));
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

  private static void printErrors(List<? extends CztError> errors)
  {
    for (CztError error : errors) {
      System.out.println(error);
      if (error.getInfo() != null) {
        System.out.println("  (" + error.getInfo() + ")");
      }
    }
  }

  public static void setConsoleLogger(Level level)
  {
    Logger rootLogger = Logger.getLogger("");
    Handler handler = null;
    Handler[] h = rootLogger.getHandlers();
    for (int i = 0; i < h.length; i++) {
      if (h[i] instanceof ConsoleHandler) {
        h[i].setLevel(level);
      }
    }
  }
}
