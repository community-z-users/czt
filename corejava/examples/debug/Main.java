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

import net.sourceforge.czt.core.ast.Spec;
import net.sourceforge.czt.core.jaxb.JaxbXmlReader;
import net.sourceforge.czt.zed.util.XmlReader;

public class Main {
  public static void main( String[] args ) {
    try {
      // Set the logger and file handler:
      // we are going to write into a file called "debug.log" ...
      Handler handler = new FileHandler("debug.log");
      // ... all messages ...
      handler.setLevel(Level.ALL);
      // ... in encoding utf8 ...
      handler.setEncoding("utf8");
      // ... for logger "debug".
      Logger.getLogger("debug").addHandler(handler);
      Logger.getLogger("debug").setLevel(Level.FINEST);

      // Create a new XML reader
      // which a new factory called DebugFactory.
      // Please have a look into DebugFactory.java to see
      // how the DebugFactory works.
      XmlReader reader = new JaxbXmlReader(new DebugFactory());

      // Load a file (see example unmarshall for a more detailed
      // description of this step).
      System.out.println("Reading file eg1.xml.");
      Spec spec =
	(Spec) reader.read(new java.io.File("../../../zml/examples/eg1.xml"));

      // After running this example, you should find logging information
      // for all method calles to DeclName in file debug.log.
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}
