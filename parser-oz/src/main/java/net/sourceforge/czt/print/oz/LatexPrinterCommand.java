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

package net.sourceforge.czt.print.oz;

import java.io.Writer;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;

public class LatexPrinterCommand
  extends net.sourceforge.czt.print.z.LatexPrinterCommand
{
  public void printLatex(Term term,
                         Writer out,
                         SectionManager sectInfo,
                         String sectionName)
  {
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(sectInfo);
    Term tree = toPrintTree(toPrintTree, term, sectionName);
    ZmlScanner scanner = new ZmlScanner(tree);
    Scanner s = scanner;
    if (sectionName == null) {
      s = createSectHeadScanner(scanner);
    }
    else {
      scanner.prepend(new Symbol(Sym.TOKENSEQ));
      scanner.append(new Symbol(Sym.TOKENSEQ));
    }
    Unicode2Latex parser = new Unicode2Latex(s);
    parser.setSectionInfo(sectInfo, sectionName);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      throw new CztException(e);
    }
  }

  /*
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
  */

  protected Term preprocess(Term term,
                            SectionManager manager,
                            String section)
    throws PrintException
  {
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(manager);
    return toPrintTree(toPrintTree, term, section);
  }

  protected TokenSequenceVisitor createTokenSequenceVisitor(Properties props)
  {
    return new TokenSequenceVisitor(props);
  }

  protected Scanner createSectHeadScanner(ZmlScanner scanner)
  {
    return new SectHeadScanner(scanner);
  }
}
