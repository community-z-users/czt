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

package net.sourceforge.czt.print.circus;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.z.PrecedenceParenAnnVisitor;
import net.sourceforge.czt.print.z.ZmlScanner.SymbolCollector;

/**
 * This Scanner uses the print visitor to tokenize a
 * given Z/Circus term.
 *
 * @author Petra Malik
 */
public class ZmlScanner
  extends net.sourceforge.czt.print.z.ZmlScanner
{
   private final List<String> warnings_;
   
  /**
   * Creates a new ZML scanner.
   */
  public ZmlScanner(Term term)
  {
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(Sym.class);
    CircusPrintVisitor visitor = new CircusPrintVisitor(collector);
    term.accept(visitor);
    warnings_ = new ArrayList<String>();
    warnings_.addAll(visitor.getWarnings());
    symbols_ = collector.getSymbols();
  }
  
  public List<String> getWarnings() {
    return Collections.unmodifiableList(warnings_);  
  }
}
