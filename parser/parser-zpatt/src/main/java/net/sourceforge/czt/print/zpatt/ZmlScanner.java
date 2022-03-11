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

package net.sourceforge.czt.print.zpatt;

import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.zpatt.ZPattKeyword;
import net.sourceforge.czt.print.z.PrecedenceParenAnnVisitor;
import net.sourceforge.czt.session.SectionInfo;

public class ZmlScanner
  extends net.sourceforge.czt.print.z.ZmlScanner
{
  /**
   * Creates a new ZML scanner.
   * @param term
   * @param props 
   */
  public ZmlScanner(SectionInfo si, Term term, Properties props)
  {
    super(si.getDialect(), props);
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(si.getDialect(), Sym.class, this);
    ZpattPrintVisitor visitor = new ZpattPrintVisitor(si, collector, props);
    term.accept(visitor);
    setSymbols(collector.getSymbols());
  }

  // Substitutes keywords as DECORWORD for Unicode printing - easier scanning
  @Override
  protected Pair<String, Object> getSymbolName(Token token)
  {
    String name = token.getName();
    Object value = token.getSpelling();
    try {
      Enum.valueOf(ZPattKeyword.class, name);
      name = "DECORWORD";
      value = new Decorword(token.spelling());
    }
    catch (IllegalArgumentException exception) {
      return super.getSymbolName(token);
    }
    return new Pair<String, Object>(name, value);
  }

  @Override
  protected Class<?> getSymbolClass()
  {
    return Sym.class;
  }
}
