/*
  Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.print.zeves;

import java.util.Iterator;
import java.util.Properties;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.print.z.PrecedenceParenAnnVisitor;
import net.sourceforge.czt.print.z.ZmlScanner.SymbolCollector;
import net.sourceforge.czt.z.util.WarningManager;

/**
 * This Scanner uses the print visitor to tokenize a
 * given Z/Circus term.
 *
 * @author Petra Malik
 */
public class ZmlScanner
  extends net.sourceforge.czt.print.z.ZmlScanner
{
  /**
   * Creates a new ZML scanner.
   * @param term
   * @param manager
   * @param prop
   */
  public ZmlScanner(Term term, WarningManager manager, Properties prop)
  {
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(Sym.class);
    ZEvesPrintVisitor visitor = new ZEvesPrintVisitor(collector, prop, manager);
    term.accept(visitor);
    symbols_ = collector.getSymbols();

  }

  public ZmlScanner(Iterator<Token> iter)
  {
    super(iter);
  }
}