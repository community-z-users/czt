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

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;
import net.sourceforge.czt.parser.util.CztScannerImpl;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public class NewlineScanner extends CztScannerImpl
{
  Scanner scanner_;
  Symbol lastToken_ = new Symbol(0);
  Symbol lastButOneToken_ = new Symbol(0);

  public NewlineScanner(Scanner scanner)
  {
    scanner_ = scanner;
  }

  @Override
  public Symbol next_token()
    throws Exception
  {
    Symbol symbol = scanner_.next_token();
    if (symbol.sym == Sym.NL) {
      int last = lastToken_.sym;
      int lastButOne = lastButOneToken_.sym;
      boolean lastTokenIsBox = Sym.ZED == last || Sym.AX == last
        || Sym.GENAX == last || Sym.GENSCH == last || Sym.ZPROOF == last ||
        Sym.ZPROOFSECTION == last;
      boolean lastIsWhere = Sym.WHERE == last;
      boolean lastButOneIsSch = Sym.SCH == lastButOne;
      if (lastTokenIsBox || lastIsWhere || lastButOneIsSch) {
        while (symbol.sym == Sym.NL) {
          symbol = scanner_.next_token();
        }
      }
    }
    lastButOneToken_ = lastToken_;
    lastToken_ = symbol;
    logSymbol(symbol);
    return symbol;
  }

  @Override
  protected Class<?> getSymbolClass()
  {
    return Sym.class;
  }
}
