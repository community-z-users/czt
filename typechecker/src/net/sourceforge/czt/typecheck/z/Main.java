package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.List;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.logging.*;

import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.jaxb.*;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.impl.*;
import net.sourceforge.czt.parser.z .*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.print.z.*;

/**
 * A class for initial testing/debugging.
 */
public final class Main
{
  /**
   * Do not create instances of this class.
   */
  private Main()
  {
  }

  /**
   * The main method.
   */
  public static void main(String[] args)
  {
    //get the file name
    String filename = args[0];
    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.base").setLevel(Level.FINEST);
      SectionManager manager = new SectionManager();
      Term term = ParseUtils.parseLatexFile(filename, manager);
      SectTypeEnv sectTypeEnv = new SectTypeEnv();

      long startTime = System.currentTimeMillis();
      List errors = TypeCheckUtils.typecheck(term, manager, sectTypeEnv);
      System.err.println("Time = " + (System.currentTimeMillis() - startTime));

      //if (errors.size() == 0) {
        //JaxbXmlWriter writer = new JaxbXmlWriter();
        //writer.write(term, System.out);
      //}

    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}

