package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.parser.z.*;

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
    String filename =
      //"mytoolkit.tex";
      "tests/test.tex";
    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.base").setLevel(Level.FINEST);
      SectTypeEnv sectTypeEnv = new SectTypeEnv();
      OperatorTable table = new OperatorTable();
      TypeAnnotatingVisitor visitor =
	new TypeAnnotatingVisitor(sectTypeEnv);
      Term term = ParseUtils.parseLatexFile(filename, table);
      term.accept(visitor);
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

