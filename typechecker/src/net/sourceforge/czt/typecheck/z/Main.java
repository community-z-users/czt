package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.dom.DomXmlWriter;
import net.sourceforge.czt.base.ast.Term;

public class Main {
  public static void main( String[] args ) {
    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      //handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.base").setLevel(Level.FINEST);

      // Unmarshal file eg1.xml ...
 	  //      XmlReader reader = new JaxbXmlReader();
	  //      Term spec = (Term) reader.read(new java.io.File("../toolkit/prelude.xml"));

      // visiting using SubstVisitor
      TypeChecker visitor = new TypeChecker();
      Term result = visitor.checkFile("src/net/sourceforge/czt/typecheck/toolkit/prelude.xml");

   	  //      Term result = (Term) spec.accept(visitor);

      // ... and marshal the result to stdout.
      //XmlWriter writer = new DomXmlWriter();
      //FileOutputStream file = new FileOutputStream ("new_prelude.xml");
      //writer.write(result, file);
      //writer.write(result, System.out);
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}

