/*
  Copyright (C) 2006, 2007 Petra Malik
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

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;


import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.session.*;

public class LatexPrinterCommand
  extends AbstractLatexPrinterCommand
  implements Command
{
  @Override
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    try {
      final Writer writer = new StringWriter();
      final Key<Term> key = new Key<Term>(name, Term.class);
      final Term term = manager.get(key);
      printLatex(term, writer, manager, null);
      writer.close();
      manager.put(new Key<LatexString>(name, LatexString.class),
                  new LatexString(writer.toString()));
      return true;
    }
    catch (IOException e) {
      throw new CommandException(e);
    }
  }

  /**
   * Prints a given term (usually an Expr or Pred) as latex markup to
   * the given writer.  The name of section (where this term belongs
   * to) and the section information is used to obtain the operator
   * table and latex markup table needed for printing.  The section
   * information should therefore be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>
   * and
   * <code>net.sourceforge.czt.parser.util.LatexMarkupTable.class</code>.
   * @param term 
   * @param out
   * @param sectInfo
   * @param sectionName
   */
  public void printLatex(Term term,
                         Writer out,
                         SectionManager sectInfo,
                         String sectionName)
  {
    TokenSequence tseq = toUnicode(term, sectInfo, sectionName,
                                   sectInfo.getProperties());
    ZmlScanner scanner = new ZmlScanner(tseq.iterator());
    Unicode2Latex parser = new Unicode2Latex(prepare(scanner, term));
    parser.setSectionInfo(sectInfo, sectionName);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      String msg = "An exception occurred while trying to print " +
        "LaTeX markup for term within section " + sectionName;
      throw new PrintException(msg, e);
    }
  }
}
