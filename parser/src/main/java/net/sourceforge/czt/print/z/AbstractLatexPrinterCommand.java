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

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

public class AbstractLatexPrinterCommand
  extends AbstractPrinterCommand
{
  protected Scanner prepare(ZmlScanner scanner, Term term)
  {
    Scanner result = scanner;
    if (term instanceof Spec || term instanceof ZSect) {
      result = new SectHeadScanner(scanner);
    }
    else if (term instanceof Para) {
      scanner.prepend(new Symbol(Sym.PARA_START));
      scanner.append(new Symbol(Sym.PARA_END));
    }
    else {
      scanner.prepend(new Symbol(Sym.TOKENSEQ));
      scanner.append(new Symbol(Sym.TOKENSEQ));
    }
    return result;
  }
}
