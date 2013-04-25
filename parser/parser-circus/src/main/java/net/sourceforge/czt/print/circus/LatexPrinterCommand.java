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
package net.sourceforge.czt.print.circus;

import java.io.Writer;
import java.util.Collections;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.print.z.Unicode2Latex;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;


public class LatexPrinterCommand 
  extends net.sourceforge.czt.print.z.LatexPrinterCommand
{
    @Override
    public void printLatex(Term term,
                         Writer out,
                         SectionManager sectInfo,
                         String sectionName) throws PrintException
  {    
    UnicodePrinter printer = new UnicodePrinter(out);
    TokenSequence tseq = toUnicode(printer, term, sectInfo, sectionName,
                                   sectInfo.getProperties());
    ZmlScanner scanner = new ZmlScanner(sectInfo.getDialect(), tseq.iterator(), sectInfo.getProperties());
    Unicode2Latex parser = new Unicode2Latex(prepare(scanner, term), sectInfo, sectInfo.getProperties(), 
    		Collections.<Key<?>>emptySet());
    parser.setSectionInfo(sectInfo, sectionName);
    parser.setWriter(printer);
    parse(out, sectInfo, parser, sectionName);

    printer = null;
    tseq = null;
    scanner = null;
    parser = null;
  }

  @Override
  protected Term preprocess(Term term,
                            SectionManager manager,
                            String section)
    throws PrintException
  {
    PrintUtils.warningManager_.setCurrentSectName(section);
    AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(manager, PrintUtils.warningManager_);
    return toPrintTree(toPrintTree, term, section);
  }

  @Override
  protected net.sourceforge.czt.print.z.TokenSequenceVisitor createTokenSequenceVisitor(
		  SectionInfo si, ZPrinter printer, Properties props)
  {
    return new TokenSequenceVisitor(si, printer, props, PrintUtils.warningManager_);
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
