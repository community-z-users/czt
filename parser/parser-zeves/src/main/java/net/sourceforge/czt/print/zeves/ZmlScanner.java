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
import net.sourceforge.czt.java_cup.runtime.Symbol;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.zeves.ZEvesProofKeyword;
import net.sourceforge.czt.parser.zeves.ZEvesSymMap;
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
    super(prop);
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(Sym.class, this);
    ZEvesPrintVisitor visitor = new ZEvesPrintVisitor(collector, prop, manager);
    term.accept(visitor);
    symbols_ = collector.getSymbols();

  }

  public ZmlScanner(Iterator<Token> iter, Properties props)
  {
    super(iter, props);
  }

  @Override
  public Symbol next_token()
  {
    Symbol result = super.next_token();
    //getSymbolMap().get(result.sym);
    //ZEvesSymMap.ALL_ZEVES_KEYWORDS
    //logSymbol(result);
    return result;
  }

  // Substitutes keywords as DECORWORD for Unicode printing - easier scanning
  @Override
  protected Pair<String, Object> getSymbolName(Token token)
  {
    String name = token.getName();
    Object value = token.getSpelling();
    try {
      // Due to the rather annoying asymmetry for the THEOREM token as a keyword/token marker
      // in both Parser and Unicode2Latex, we need to *not* consider THMUSAGE here as keywords
      if (!ZEvesSymMap.ALL_ZEVES_USAGE_WORDS.contains(name))
      {
        Enum.valueOf(ZEvesProofKeyword.class, name);
        name = "DECORWORD";
        value = new Decorword(token.spelling());
      }
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