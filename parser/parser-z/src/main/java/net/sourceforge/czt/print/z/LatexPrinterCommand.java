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
import java.text.MessageFormat;
import java.util.Collections;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

public class LatexPrinterCommand
  extends AbstractLatexPrinterCommand
{
  /**
   * Given a section or spec name (e.g., it uses TermCommand) it computes the term
   * to be printed as LaTeX output, and added to the Manager as a LatexString class.
   * We wrap it up with usual LaTeX markup if property is requested in the manager.
   * @param name
   * @param manager
   * @return
   * @throws CommandException
   */
  @Override
  protected boolean doCompute(String name, SectionManager manager)
    throws CommandException
  {
    try {
      traceLog("LATEX-PRINT = " + name);
      final Writer writer = new StringWriter();
      final Key<Term> key = new Key<Term>(name, Term.class);
      final Term term = manager.get(key);
      if (term instanceof ZSect)
        printLatex(term, writer, manager, name);
      else
        // in case of spec (e.g., multiple  or anonymous sections; or on-the-fly, don't give sectionName)
        printLatex(term, writer, manager, onTheFlySectName_);
      writer.close();
      manager.endTransaction(new Key<LatexString>(name, LatexString.class),
                  new LatexString(writer.toString()));
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
                         String sectionName) throws PrintException
  {
	if (out == null || sectInfo == null || term == null) throw new NullPointerException();
	//if (!(sectInfo instanceof SectionManager)) throw new IllegalArgumentException("Invalid section manager implementation ");
    Properties props = sectInfo.getProperties();
    UnicodePrinter printer = new UnicodePrinter(out);
    TokenSequence tseq = toUnicode(printer, term, sectInfo, sectionName, props);
    ZmlScanner scanner = new ZmlScanner(sectInfo.getDialect(), tseq.iterator(), props);
    Unicode2Latex parser = new Unicode2Latex(prepare(scanner, term), sectInfo, props, Collections.<Key<?>>emptySet());
    parser.setSectionInfo(sectInfo, sectionName);
    parser.setWriter(printer);
    parse(out, sectInfo, parser, sectionName);

    printer = null;
    tseq = null;
    scanner = null;
    parser = null;
  }

  protected void parse(Writer out, SectionManager sectInfo, java_cup.runtime.lr_parser parser, String sectionName) throws PrintException
  {
	if (out == null || sectInfo == null || parser == null) throw new NullPointerException();
    try
    {
      latexPreamble(out, sectInfo);
      parser.parse();
      latexPostscript(out, sectInfo);
    }
    catch (Exception e)
    {
      throw new PrintException(sectInfo.getDialect(),
    		  	MessageFormat.format(ZPrintMessage.MSG_PRINT_LATEX_EXCEPTION.getMessage(), "LaTeX", sectionName), e);
    }
  }
}
