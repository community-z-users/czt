/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.rules.print;

import java.io.Writer;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.z.PrecedenceParenAnnVisitor;
import net.sourceforge.czt.print.z.UnicodePrinter;
import net.sourceforge.czt.print.zpatt.ZpattPrintVisitor;
import net.sourceforge.czt.session.*;
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

  /**
   * Prints a given term (usually an Expr or Pred) as unicode to the
   * given writer.  The name of section (where this term belongs to)
   * and the section information is used to obtain the operator table
   * and latex markup table needed for printing.  The section
   * information should therefore be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   *
   * This method may be used for terms like Expr and Pred that do not
   * contain a section header so that context information cannot be
   * obtained from the tree itself.  See
   * {@link #printUnicode(Term,Writer,SectionManager)} for writing trees that do
   * contain context information.
   */
  public static void printUnicode(Term term,
                                  Writer out,
                                  SectionManager sectInfo,
                                  String sectionName)
  {
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(sectInfo);
    Term tree;
    try {
      tree = (Term) toPrintTree.run(term, sectionName);
    }
    catch (CommandException exception) {
      throw new CztException(exception);
    }
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    tree.accept(precVisitor);
    UnicodePrinter printer = new UnicodePrinter(out);
    Properties props = sectInfo.getProperties();
    ZpattPrintVisitor visitor = new ZpattPrintVisitor(printer, props);
    tree.accept(visitor);
  }
}
