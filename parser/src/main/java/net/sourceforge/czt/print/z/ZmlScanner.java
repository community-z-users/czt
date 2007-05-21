/*
  Copyright (C) 2004, 2006 Petra Malik
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
import java.util.Map;
import java.util.Properties;
import java.util.Vector;

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;

/**
 * This Scanner uses the print visitor to tokenize a
 * given Z term.
 *
 * @author Petra Malik
 */
public class ZmlScanner
  implements Scanner
{
  protected List symbols_;
  private int pos_ = 0;

  /**
   * Creates a new ZML scanner.
   */
  public ZmlScanner()
  {
  }

  public ZmlScanner(Term term)
  {
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(Sym.class);
    ZPrintVisitor visitor = new ZPrintVisitor(collector);
    term.accept(visitor);
    symbols_ = collector.getSymbols();
  }

  /**
   * Creates a new ZML scanner.
   */
  public ZmlScanner(Term term, Properties properties)
  {
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(Sym.class);
    ZPrintVisitor visitor = new ZPrintVisitor(collector, properties);
    term.accept(visitor);
    symbols_ = collector.getSymbols();
  }

  public void prepend(Symbol s)
  {
    symbols_.add(0, s);
  }

  public void append(Symbol s)
  {
    symbols_.add(s);
  }

  public Symbol next_token()
  {
    if (pos_ >= symbols_.size()) return new Symbol(0);
    Symbol result = (Symbol) symbols_.get(pos_);
    pos_++;
    return result;
  }

  public static int getIntValue(String tokenName,
                                Map<String, Object> fieldMap)
  {
    Object object = fieldMap.get(tokenName);
    if (object instanceof Integer) {
      Integer result = (Integer) object;
      return result;
    }
    throw new CztException(tokenName.toString() + " not found.");
  }

  /**
   * An implementation of AbstractPrintVisitor.ZPrinter.
   */
  public static class SymbolCollector
    implements AbstractPrintVisitor.ZPrinter
  {
    private List<Symbol> symbolList_ = new Vector<Symbol>();
    private Map<String, Object> fieldMap_;

    public SymbolCollector(Class clazz)
    {
      fieldMap_ = DebugUtils.getFieldMap2(clazz);
    }

    public void printToken(Token token)
    {
      int intValue = getIntValue(token.getName(), fieldMap_);
      symbolList_.add(new Symbol(intValue,
                                 token.getSpelling()));
    }

    public List<Symbol> getSymbols()
    {
      return symbolList_;
    }
  }
}
