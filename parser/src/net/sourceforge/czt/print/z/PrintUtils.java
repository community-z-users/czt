/**
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.io.Writer;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;

/**
 * Utilities for printing Z specifications given as an AST.
 *
 * @author Petra Malik
 */
public final class PrintUtils
{
  /**
   * Do not create instances of this class.
   */
  private PrintUtils()
  {
  }

  public static void printLatex(Term term, Writer out, SectionManager manager)
  {
    Term tree = term;
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor();
    tree = (Term) tree.accept(toPrintTree);
    EqualPredVisitor visitor = new EqualPredVisitor();
    tree = (Term) tree.accept(visitor);
    ZmlScanner scanner = new ZmlScanner(tree, manager);
    Unicode2Latex parser = new Unicode2Latex(scanner);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      throw new CztException(e);
    }
  }

  public static void printUnicode(Term term, Writer out,
                                  SectionManager manager)
  {
    Term tree = term;
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor();
    tree = (Term) tree.accept(toPrintTree);
    EqualPredVisitor visitor = new EqualPredVisitor();
    tree = (Term) tree.accept(visitor);
    ZmlScanner scanner = new ZmlScanner(tree, manager);
    UnicodePrinter printer = new UnicodePrinter(out);
    printer.printZed(scanner);
  }
}
