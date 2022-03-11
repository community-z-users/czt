/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

public class UnicodePrinterCommand
  extends AbstractPrinterCommand
{
  @Override
  protected boolean doCompute(String name, SectionManager manager)
    throws CommandException
  {
    try {
      final Writer writer = new StringWriter();
      final Key<Term> key = new Key<Term>(name, Term.class);
      final Term term = manager.get(key);
      if (term instanceof ZSect)
        printUnicode(term, writer, manager, name);
      else
        // in case of spec (e.g., multiple  or anonymous sections; or on-the-fly, don't give sectionName)
        printUnicode(term, writer, manager, onTheFlySectName_);
      writer.close();
      manager.endTransaction(new Key<UnicodeString>(name, UnicodeString.class),
                  new UnicodeString(writer.toString()));
      return true;
    }
    catch (IOException e) {
      throw new CommandException(manager.getDialect(), e);
    }
    catch (PrintException pe)
    {
      throw new CommandException(manager.getDialect(), pe);
    }
  }

  /**
   * Prints a given term (usually an Expr or Pred) as unicode to the
   * given writer.  The name of section (where this term belongs to)
   * and the section information is used to obtain the operator table
   * and latex markup table needed for printing.  The section
   * information should therefore be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   * @param term
   * @param out
   * @param sectInfo
   * @param sectionName
   */
  public void printUnicode(Term term,
                           Writer out,
                           SectionManager sectInfo,
                           String sectionName) throws PrintException
  {
    if (out == null || sectInfo == null || term == null) throw new NullPointerException();
    Properties props = sectInfo.getProperties();
    //ZPrinter printer = new NewlinePrinter(new UnicodePrinter(out));
    ZPrinter printer = new UnicodePrinter(out);
    TokenSequence tseq = toUnicode(printer, term, sectInfo, sectionName, props);
    printer.printToken(tseq);
    tseq = null;
    printer = null;
    props = null;
  }
}
