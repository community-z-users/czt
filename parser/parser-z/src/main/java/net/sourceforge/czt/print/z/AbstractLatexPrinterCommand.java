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
import java.io.Writer;

import java_cup.runtime.Symbol;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.CztScanner;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

public abstract class AbstractLatexPrinterCommand
  extends AbstractPrinterCommand implements LatexPrinterPropertyKeys
{
  private boolean latexWrapping_ = PROP_LATEXPRINTER_WRAPPING_DEFAULT;

  protected CztScanner prepare(ZmlScanner scanner, Term term)
  {
    CztScanner result = scanner;
    if (term instanceof Spec || term instanceof ZSect) {
      // do nothing
    }
    else if (term instanceof Para) {
      scanner.prepend(new Symbol(getSymParaStart()));
      scanner.append(new Symbol(getSymParaEnd()));
    }
    else {
      scanner.prepend(new Symbol(getSymTokenseq()));
      scanner.append(new Symbol(getSymTokenseq()));
    }
    return result;
  }

  @Override
  protected void processProperties(SectionManager manager)
  {
    super.processProperties(manager);
    latexWrapping_ = (manager.hasProperty(PROP_LATEXPRINTER_WRAPPING) ?
        manager.getBooleanProperty(PROP_LATEXPRINTER_WRAPPING) :
        PROP_LATEXPRINTER_WRAPPING_DEFAULT);
  }

  protected int getSymParaStart()
  {
    return Sym.PARA_START;
  }

  protected int getSymParaEnd()
  {
    return Sym.PARA_END;
  }

  protected int getSymTokenseq()
  {
    return Sym.TOKENSEQ;
  }

  // TODO: make it parameterised by extension?
  public final static String LATEX_PREAMBLE =
          "\\documentclass{article}\n\\usepackage{czt}\n\n\\begin{document}\n%----------------------------------\n\n";

  public final static String LATEX_POSTSCRIPT =
          "\n\n%----------------------------------\n\\end{document}";

  protected boolean getLatexWrapping()
  {
    return latexWrapping_;
  }
  
  protected void latexPreamble(Writer out, SectionInfo sectInfo) throws IOException
  {
    if (getLatexWrapping())
    {
      out.write(LATEX_PREAMBLE);
    }
  }

  protected void latexPostscript(Writer out, SectionInfo sectInfo) throws IOException
  {
    if (getLatexWrapping())
    {
      out.write(LATEX_POSTSCRIPT);
    }
  }
}

