/**
Copyright 2003 Mark Utting
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

import java_cup.runtime.Symbol;
import net.sourceforge.czt.parser.util.CztScanner;
import net.sourceforge.czt.parser.util.CztScannerImpl;
import net.sourceforge.czt.session.Dialect;

/**
 * This scanner gets token from another scanner and provides them
 * to the parser, but removes some of the NL tokens.
 *
 * @author Petra Malik
 */
public class NewlineScanner
  extends CztScannerImpl
{
  private final CztScanner scanner_;
  private Symbol lastToken_ = new Symbol(0);
  private Symbol lastButOneToken_ = new Symbol(0);

  public NewlineScanner(CztScanner scanner)
  {
    scanner_ = scanner;
  }

  protected boolean isBoxSymbol(int sym)
  {
    return Sym.ZED == sym || Sym.AX == sym
        || Sym.GENAX == sym || Sym.GENSCH == sym;
  }

  protected boolean isWhereSymbol(int sym)
  {
    return Sym.WHERE == sym;
  }

  protected boolean isSchSymbol(int sym)
  {
    return Sym.SCH == sym;
  }

  protected int getNLSym()
  {
    return Sym.NL;
  }

  @Override
  public Symbol next_token()
    throws Exception
  {
    Symbol symbol = scanner_.next_token();
    if (symbol.sym == getNLSym()) {
      int last = lastToken_.sym;
      int lastButOne = lastButOneToken_.sym;
      boolean lastTokenIsBox = isBoxSymbol(last);
      boolean lastIsWhere = isWhereSymbol(last);
      boolean lastButOneIsSch = isSchSymbol(lastButOne);
      if (lastTokenIsBox || lastIsWhere || lastButOneIsSch) {
        while (symbol.sym == getNLSym()) {
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

	@Override
	public Dialect getDialect() {
		return scanner_.getDialect();
	}
}
