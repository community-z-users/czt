package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.parser.z .*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.print.z.*;

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
      "tests/newtest.tex";
    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.base").setLevel(Level.FINEST);
      SectTypeEnv sectTypeEnv = new SectTypeEnv(true);
      //OpTable table = new OpTable();
      SectionManager manager = new SectionManager();
      TypeAnnotatingVisitor typeVisitor =
	new TypeAnnotatingVisitor(sectTypeEnv, manager);
      TypeChecker typechecker = new TypeChecker(manager);
      Term term = ParseUtils.parseLatexFile(filename, manager);
      term.accept(typeVisitor);
      term.accept(typechecker);
      //XmlWriter writer = new JaxbXmlWriter();
      //FileOutputStream file = new FileOutputStream ("new_prelude.xml");
      //writer.write(result, file);
      //writer.write(result, System.out);

//      AbstractPrintVisitor.ZPrinter zPrinter =
//	UnicodePrinter(new PrintWriter(System.err));
//      ZPrintVisitor zPrintVisitor = new ZPrintVisitor(zPrinter);
	
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}

