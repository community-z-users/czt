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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.base.util.XmlWriter;

import net.sourceforge.czt.z.ast.Spec;

public class Main {
  // This sample application demonstrates how to
  // read and write an Object Z specification.

  public static void main(String[] args) {
    // Use a default file name ...
    String fileName = "oz.xml";
    // ... or the file provided as an argument.
    if (args.length > 0) fileName = args[0];

    XmlReader reader;
    XmlWriter writer;
    
    try {

      // When using the Z-XmlReader for an object Z specification,
      // an exception is thrown
      reader = new net.sourceforge.czt.z.jaxb.JaxbXmlReader();
      try {
        System.out.println("Using the Z XmlReader for reading object Z:");
        System.out.println("-------------------------------------------");
        reader.read(new java.io.File(fileName));
      } catch(Exception e) {
        System.out.println("Exception caught");
        e.printStackTrace(System.out);
      }

      // Using the OZ-XmlReader should work
      reader = new net.sourceforge.czt.oz.jaxb.JaxbXmlReader();
      Term term = reader.read(new java.io.File(fileName));

      // When using the Z-XmlWriter for an object Z specification,
      // an exception is thrown
      writer = new net.sourceforge.czt.z.jaxb.JaxbXmlWriter();
      try {
        System.out.println("Using the Z XmlWriter for writing object Z:");
        System.out.println("-------------------------------------------");
        writer.write(term, System.out);
      } catch(Exception e) {
        System.out.println("Exception caught");
        e.printStackTrace(System.out);
      }
      // using the OZ-XmlWriter should work
      writer = new net.sourceforge.czt.oz.jaxb.JaxbXmlWriter();
      System.out.println("Using the OZ XmlWriter for writing object Z:");
      System.out.println("--------------------------------------------");
      writer.write(term, System.out);
    } catch(Exception e) {
      e.printStackTrace();
    }
  }
}
