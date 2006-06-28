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

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;

public class Main
{
  public static String PREFIX = "java -jar czt.jar ";

  public static void main(String[] args)
    throws Throwable
  {
    if (args.length == 0) System.out.println(usage());
    else if ("-e".equals(args[0])) {
      if (args.length < 3) {
        System.out.println(usage());
      }
      else {
        SectionManager manager = new SectionManager(args[1]);
        parse(args[2], manager);
      }
    }
    else if (args[0].contains(".")) {
      SectionManager manager = new SectionManager();
      parse(args[0], manager);
    }
    else {
      command(args);
    }
  }

  public static String usage()
  {
    return usage(PREFIX);
  }

  public static String usage(String prefix)
  {
    return "Usage:\n" +
      prefix + "[-e <extension>] <filename>\n" +
      prefix + "<command> [<commandArg1> .. <commandArgN>]";
  }

  /**
   * The first string contains the command to be invoked,
   * the following are arguments to the command.
   */
  public static void command(String[] args)
    throws Throwable
  {
    URL url = Main.class.getResource("command.properties");
    Properties props = new Properties();
    InputStream is = url.openStream();
    if (is != null) {
      props.loadFromXML(is);
      final String name = props.getProperty(args[0]);
      if (name == null) {
        System.err.println("Cannot find tool " + args[0]);
        System.err.println("Available tools are:");
        for(Map.Entry entry : props.entrySet()) {
          System.err.println("  " + entry.getKey() +
                             " (bound to " + entry.getValue() + ")");
        }
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
    else {
      throw new RuntimeException("Cannot read resource command.properties");
    }
  }

  public static void parse(String filename, SectionManager manager)
    throws CommandException
  {
    try {
      FileSource source = new FileSource(filename);
      String name = source.getName();
      manager.put(new Key(name, Source.class), source);
      Spec spec = (Spec) manager.get(new Key(name, Spec.class));
      if (spec.getSect().size() > 0) {
        for (Sect sect : spec.getSect()) {
          if (sect instanceof ZSect) {
            manager.get(new Key(((ZSect) sect).getName(),
                                SectTypeEnvAnn.class));
          }
        }
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
      }
      else {
        throw exception;
      }
    }
  }

  private static void printErrors(List<? extends CztError> errors)
  {
    for (CztError error : errors) {
      System.out.println(error);
    }
  }
}
