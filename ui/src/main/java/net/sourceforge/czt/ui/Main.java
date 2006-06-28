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

import net.sourceforge.czt.session.*;

public class Main
{
  public static void main(String[] args)
    throws Throwable
  {
    if (args[0].contains(".")) {
      System.err.println("Not yet implemented");
      return;
    }
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
}
