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

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.zed.util.*;
import net.sourceforge.czt.core.jaxb.JaxbXmlReader;
import net.sourceforge.czt.core.dom.DomXmlWriter;
import net.sourceforge.czt.zed.ast.Term;

public class Main {
  public static void main( String[] args ) {
    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.core.util").setLevel(Level.FINEST);

      // Unmarshal file eg1.xml ...
      XmlReader reader = new JaxbXmlReader();
      Term spec =
	(Term) reader.read(new java.io.File("../../../zml/examples/eg1.xml"));

      // visiting using SubstVisitor
      SubstVisitor visitor = new SubstVisitor();
      Term result = (Term) spec.accept(visitor);

      // ... and marshal the result to stdout.
      XmlWriter writer = new DomXmlWriter();
      writer.write(result, System.out);
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}
