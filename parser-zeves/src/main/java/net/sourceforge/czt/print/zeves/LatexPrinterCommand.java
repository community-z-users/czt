/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.print.zeves;

import java.io.Writer;
import java.util.Properties;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.TokenSequence;
import net.sourceforge.czt.print.z.AstToPrintTreeVisitor;
import net.sourceforge.czt.print.z.UnicodePrinter;
import net.sourceforge.czt.session.SectionManager;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public class LatexPrinterCommand
        extends net.sourceforge.czt.print.z.LatexPrinterCommand
{
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
  protected TokenSequenceVisitor createTokenSequenceVisitor(Properties props)
  {
    return new TokenSequenceVisitor(props, PrintUtils.warningManager_);
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
