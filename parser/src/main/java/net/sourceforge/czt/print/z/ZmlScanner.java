/*
  Copyright (C) 2004, 2006, 2007 Petra Malik
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

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Vector;

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZOpToken;
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

  private Iterator<Token> iter_;
  private Symbol pre_;
  private Symbol post_;

  /**
   * Creates a new ZML scanner.
   */
  protected ZmlScanner()
  {
  }

  public ZmlScanner(Iterator<Token> iter)
  {
    iter_ = iter;
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
    if (iter_ != null) {
      pre_ = s;
    }
    else {
      symbols_.add(0, s);
    }
  }

  public void append(Symbol s)
  {
    if (iter_ != null) {
      post_ = s;
    }
    else {
      symbols_.add(s);
    }
  }

  public Symbol next_token()
  {
    if (iter_ != null) {
      Symbol result = null;
      if (pre_ != null) {
        result = pre_;
        pre_ = null;
        return result;
      }
      if (iter_.hasNext()) {
        result = getSymbol(iter_.next(), DebugUtils.getFieldMap2(Sym.class));
      }
      if (result == null) {
        if (post_ != null) {
          result = post_;
          post_ = null;
        }
        else {
          result = new Symbol(0);
        }
      }
      return result;
    }
    if (pos_ >= symbols_.size()) return new Symbol(0);
    Symbol result = (Symbol) symbols_.get(pos_);
    pos_++;
    return result;
  }

  public static Symbol getSymbol(Token token,
                                 Map<String, Object> fieldMap)
  {
    String name = token.getName();
    Object value = token.getSpelling();
    try {
      Enum.valueOf(ZOpToken.class, name);
      name = "DECORWORD";
    }
    catch (IllegalArgumentException exception) {
      try {
        Enum.valueOf(ZKeyword.class, name);
        name = "DECORWORD";
        value = new Decorword(token.spelling());
      }
      catch (IllegalArgumentException e) {
      }
    }
    Object object = fieldMap.get(name);
    if (object instanceof Integer) {
      Integer result = (Integer) object;
      return new Symbol(result, value);
    }
    throw new CztException(token.getName() + " not found.");
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
      symbolList_.add(getSymbol(token, fieldMap_));
    }

    public List<Symbol> getSymbols()
    {
      return symbolList_;
    }
  }
}
