package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.typecheck.util.typingenv.*;
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
    //another comment
    String filename =
      //"mytoolkit.tex";
      "tests/newtest.tex";
    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.base").setLevel(Level.FINEST);
      SectTypeEnv sectTypeEnv = new SectTypeEnv();
      SectionManager manager = new SectionManager();
      TypeAnnotatingVisitor typeVisitor =
        new TypeAnnotatingVisitor(sectTypeEnv, manager);
      TypeChecker typechecker = new TypeChecker(manager);
      Term term = ParseUtils.parseLatexFile(filename, manager);
      term.accept(typeVisitor);
      term.accept(typechecker);
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}

