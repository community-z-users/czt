/**
Copyright 2004 Petra Malik
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

import java.util.List;
import java.util.Vector;

import java_cup.runtime.Scanner;
import java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;

import net.sourceforge.czt.session.SectionManager;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * This Scanner uses the print visitor to tokenize a
 * given Z term.
 *
 * @author Petra Malik
 */
public class ZmlScanner
  implements Scanner
{
  private List symbols_;
  private int pos_ = 0;

  public ZmlScanner(Term term, SectionManager manager)
  {
    SymbolCollector collector = new SymbolCollector();
    ZPrintVisitor visitor = new ZPrintVisitor(collector, manager);
    term.accept(visitor);
    symbols_ = collector.getSymbols();
  }

  public Symbol next_token()
  {
    if (pos_ >= symbols_.size()) return new Symbol(0);
    Symbol result = (Symbol) symbols_.get(pos_);
    pos_++;
    return result;
  }

  /**
   * An implementation of AbstractPrintVisitor.ZPrinter.
   */
  private static class SymbolCollector
    implements AbstractPrintVisitor.ZPrinter
  {
    private List symbolList_ = new Vector();

    public void printSymbol(Symbol symbol)
    {
      symbolList_.add(symbol);
    }

    public List getSymbols()
    {
      return symbolList_;
    }
  }
}
