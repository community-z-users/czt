package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;

public final class Main
{
  /**
   * Do not create instances of this class.
   */
  private Main()
  {
  }

  public static void main( String[] args )
  {
    String filename = "src/net/sourceforge/czt/typecheck/toolkit/prelude.xml";
    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.base").setLevel(Level.FINEST);
      TypeChecker visitor = new TypeChecker();
      Term result = visitor.checkFile(filename);
      //XmlWriter writer = new JaxbXmlWriter();
      //FileOutputStream file = new FileOutputStream ("new_prelude.xml");
      //writer.write(result, file);
      //writer.write(result, System.out);
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}

