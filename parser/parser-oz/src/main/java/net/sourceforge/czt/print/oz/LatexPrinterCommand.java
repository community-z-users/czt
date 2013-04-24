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
import java.util.Collections;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;

public class LatexPrinterCommand
  extends net.sourceforge.czt.print.z.LatexPrinterCommand
{
  @Override
  public void printLatex(Term term,
                         Writer out,
                         SectionManager sectInfo,
                         String sectionName) throws PrintException
  {
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(sectInfo);
    Term tree = toPrintTree(toPrintTree, term, sectionName);
    ZmlScanner scanner = new ZmlScanner(sectInfo, tree, sectInfo.getProperties());
    Unicode2Latex parser = new Unicode2Latex(prepare(scanner, term), sectInfo, 
    		sectInfo.getProperties(), Collections.<Key<?>>emptySet());
    parser.setSectionInfo(sectInfo, sectionName);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      throw new CztException(e);
    }

    tree = null;
    scanner = null;
    parser = null;
    printer = null;
  }

  /* That's how I expect it to work (using the pretty printer)
  @Override
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

  @Override
  protected Term preprocess(Term term,
                            SectionManager manager,
                            String section)
    throws PrintException
  {
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(manager);
    return toPrintTree(toPrintTree, term, section);
  }

  @Override
  protected net.sourceforge.czt.print.z.TokenSequenceVisitor createTokenSequenceVisitor(
		  SectionInfo si, ZPrinter printer, Properties props)
  {
    return new TokenSequenceVisitor(si, printer, props);
  }

  @Override
  protected int getSymParaStart()
  {
    return Sym.PARA_START;
  }

  @Override
  protected int getSymParaEnd()
  {
    return Sym.PARA_END;
  }

  @Override
  protected int getSymTokenseq()
  {
    return Sym.TOKENSEQ;
  }
}
