/*
  Copyright 2004, 2005, 2006 Petra Malik
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

import java.util.Map;

import net.sourceforge.czt.java_cup.runtime.Symbol;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.parser.util.DebugUtils;

/**
 * A Z visitor used for printing.
 *
 * @author Petra Malik
 */
public abstract class AbstractPrintVisitor
  implements Visitor
{
  private ZPrinter printer_;

  public AbstractPrintVisitor(ZPrinter printer)
  {
    printer_ = printer;
  }

  public ZPrinter getPrinter()
  {
    return printer_;
  }

  protected void print(int type, int ext)
  {
    printer_.printSymbol(new Symbol(type, ext, -1));
  }

  protected void print(int type, int ext, Object value)
  {
    printer_.printSymbol(new Symbol(type, ext, -1, value));
  }

  /**
   * A printer that can print Z symbols.
   */
  public interface ZPrinter
  {
    void printSymbol(Symbol symbol);
  }
}
