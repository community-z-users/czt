/**
Copyright 2003 Mark Utting
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

import java.util.logging.*;

import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.base.util.XmlReader;

public class Main {
  public static void main( String[] args ) {
    String logFileName = "debug.log";
    // Use a default file name ...
    String fileName = "../../../zml/examples/eg1.xml";
    // ... or the file provided as an argument.
    if (args.length > 0) fileName = args[0];

    try {
      // Set the logger and file handler:
      // we are going to write into the file logFileName
      Handler handler = new FileHandler(logFileName);
      // ... all messages ...
      handler.setLevel(Level.ALL);
      // ... in encoding utf8 ...
      handler.setEncoding("utf8");
      // ... for logger "debug".
      Logger.getLogger("debug").addHandler(handler);
      Logger.getLogger("debug").setLevel(Level.FINEST);

      // Create a new XML reader
      // which uses a new factory called DebugFactory.
      // Please have a look into DebugFactory.java to see
      // how the DebugFactory works.
      XmlReader reader = new JaxbXmlReader(new DebugFactory());

      // Load a file (see example unmarshall for a more detailed
      // description of this step).
      System.out.println("Reading file " + fileName + ".");
      Spec spec =
	(Spec) reader.read(new java.io.File(fileName));

      System.out.println("\nYou should find logging information ");
      System.out.println("for all method calls to DeclName in file " + logFileName + ".");
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}
