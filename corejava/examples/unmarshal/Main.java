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

import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlReader;

public class Main {
  // This sample application demonstrates how to
  // unmarshall (read) a Z specification written in ZML.
  // In order to unmarshall an object Z specification,
  // use the JaxbXmlReader provided in net.sourceforge.czt.oz.jaxb.

  public static void main(String[] args) {
    // Use a default file name ...
    String fileName = "../../../zml/examples/eg1.xml";
    // ... or the file provided as an argument.
    if (args.length > 0) fileName = args[0];
    
    try {
      // Create a new XML reader.
      XmlReader reader = new JaxbXmlReader();

      // Read the file.
      System.out.print("Reading file " + fileName + " ...");
      Term term = reader.read(new java.io.File(fileName));
      System.out.println(" done.");

      // Now we have got an AST representation of the file.
      // You may read and edit the AST now ...
      System.out.println("The root element of the AST is " + term + ".");
      if (term instanceof Spec) {
	Spec spec = (Spec) term;
	System.out.println("The specification contains " +
			   spec.getSect().size() +
			   " section(s).");
      }
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}
