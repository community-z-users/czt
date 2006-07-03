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

package net.sourceforge.czt.ui;

import java.io.*;
import java.lang.reflect.*;
import java.net.URL;
import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.print.util.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;

public class Main
{
  public static String PREFIX = "java -jar czt.jar ";

  public static void main(String[] args)
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
      Level verbosityLevel = Level.WARNING;
      for (int i = 0; i < args.length; i++) {
        if ("-s".equals(args[i])) {
          syntaxCheckOnly = true;
        }
        else if ("-v".equals(args[i])) {
          verbosityLevel = Level.INFO;
        }
        else if ("-vv".equals(args[i])) {
          verbosityLevel = Level.FINER;
          Logger.getLogger("").setLevel(verbosityLevel);
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
          setConsoleLogger(verbosityLevel);
          SectionManager manager = new SectionManager(extension);
          FileSource source = new FileSource(args[i]);
          if (parse(source, manager, syntaxCheckOnly) && output != null) {
            if (output.endsWith("utf8")) {
              UnicodeString unicode = (UnicodeString)
                manager.get(new Key(source.getName(), UnicodeString.class));
              FileOutputStream stream = new FileOutputStream(output);
              Writer writer = new OutputStreamWriter(stream, "UTF-8");
              writer.write(unicode.toString());
              writer.close();
            }
            else if (output.endsWith("utf16")) {
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
              Writer writer = new OutputStreamWriter(stream);
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

  public static String usage()
  {
    return usage(PREFIX);
  }

  public static String usage(String prefix)
  {
    return "Usage:\n" +
      "  " + prefix + "[-d <dialect>] [-o <filename>] [-s] <filename>\n" +
      "  " + prefix + "<command> [<commandArg1> .. <commandArgN>]\n" +
      "Flags:\n  -d   specify the dialect to be used\n" +
      "  -o   specifiy output file (mark-up is determined by file ending)\n" +
      "  -s   syntax check only\n" +
      "Dialects:\n  z    Standard Z (default)\n  oz   Object Z\n" +
      "File ending bingings:\n  tex, zed --> LaTeX Markup\n" +
      "  xml, zml --> ZML\n" +
      "  utf8     --> Unicode (encoding UTF-8)\n" +
      "  utf16    --> Unicode (encoding UTF-16)\n" +
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
        String[] arguments = new String[args.length-1];
        for (int i = 0; i < arguments.length; i++) {
          arguments[i] = args[i+1];
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
    for(Map.Entry entry : props.entrySet()) {
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
                              boolean syntaxCheckOnly)
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
            if (zSect.getParaList() instanceof ZParaList &&
                ((ZParaList) zSect.getParaList()).size() > 0) {
	      nrOfZSects++;
	      logger.info("Z Section " + zSect.getName());
	    }
            if (! syntaxCheckOnly) {
              manager.get(new Key(zSect.getName(),
                                  SectTypeEnvAnn.class));
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
