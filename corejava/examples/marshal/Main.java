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

import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.dom.DomXmlWriter;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.base.util.XmlWriter;

public class Main {
  // This sample application demonstrates how to
  // unmarshall (read) and marshall (write)
  // a Z specification written in ZML.
  // In order to unmarshall an object Z specification,
  // use the JaxbXmlReader provided in net.sourceforge.czt.oz.jaxb.

  public static void main( String[] args ) {
    // Use a default file name ...
    String fileName = "../../../zml/examples/eg1.xml";
    // ... or the file provided as an argument.
    if (args.length > 0) fileName = args[0];

    try {
      // Unmarshal file ...
      XmlReader reader = new JaxbXmlReader();
      Term term = reader.read(new java.io.File(fileName));

      // ... and marshal it.

      // First we marshal to stdout using Jaxb.
      // Note that the default encoding of your system is used
      // and Unicode characters may not be shown properly.
      XmlWriter writer = new JaxbXmlWriter();
      System.out.println("****************************************");
      System.out.println("Marshalling using Jaxb");
      System.out.println("****************************************");
      writer.write(term, System.out);

      // Next we mashal to a file using Jaxb.
      // Note that the encoding is set to utf8 explicitly.
      OutputStreamWriter outputStream
	= new OutputStreamWriter(new FileOutputStream("test.xml"), "utf8");
      writer.write(term, outputStream);

      // Finally we use DOM.
      // Note that DOM support is experimental
      // TODO: how to set encoding?
      System.out.println();
      System.out.println("****************************************");
      System.out.println("Marshalling using DOM");
      System.out.println("(DOM support is experimental)");
      System.out.println("****************************************");
      writer = new DomXmlWriter();
      writer.write(term, System.out);
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}

