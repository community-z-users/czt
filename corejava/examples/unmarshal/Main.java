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
      // Create a new XML reader.
      XmlReader reader = new JaxbXmlReader();

      // Load a file.
      // Since we know that the root element of the file is a specification,
      // we can cast it to a Spec.
      System.out.println("Reading file eg1.xml.");
      Spec spec =
	(Spec) reader.read(new java.io.File("../../../zml/examples/eg1.xml"));

      // Now we have got an AST representation of the file.
      // You may read and edit the AST now ...
      System.out.println("The specification contains " +
			 spec.getSect().size() +
			 " section(s).");
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}
