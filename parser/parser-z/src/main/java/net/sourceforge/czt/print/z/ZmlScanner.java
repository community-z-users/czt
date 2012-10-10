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

import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZOpToken;
import net.sourceforge.czt.util.CztException;

/**
 * This Scanner uses the print visitor to tokenize a
 * given Z term.
 *
 * @author Petra Malik
 */
public class ZmlScanner
  extends CztScannerImpl
{
  protected List<Symbol> symbols_;
  private int pos_ = 0;

  private Iterator<Token> iter_;
  private Symbol pre_;
  private Symbol post_;

  /**
   * Creates a new ZML scanner.
   * @param properties
   */
  protected ZmlScanner(Properties properties)
  {
    super(properties);
  }

  public ZmlScanner(Iterator<Token> iter, Properties properties)
  {
    super(properties);
    iter_ = iter;
  }

  /**
   * Creates a new ZML scanner.
   * @param term
   * @param properties
   */
  public ZmlScanner(Term term, Properties properties)
  {
    super(properties);
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(Sym.class, this);
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

  @Override
  public Symbol next_token()
  {
    if (iter_ != null) {
      Symbol result = null;
      if (pre_ != null) {
        result = pre_;
        pre_ = null;
        logSymbol(result);
        return result;
      }
      if (iter_.hasNext()) {
        result = getSymbol(iter_.next(), getSymbolMap2());
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
      logSymbol(result);
      return result;
    }
    if (pos_ >= symbols_.size()) 
    {
      Symbol result = new Symbol(0);
      logSymbol(result);
      return result;
    }
    Symbol result = symbols_.get(pos_);
    pos_++;
    logSymbol(result);
    return result;
  }

  // Substitutes keywords as DECORWORD for Unicode printing - easier scanning
  protected Pair<String, Object> getSymbolName(Token token)
  {
    String name = token.getName();
    Object value = token.getSpelling();
    try {
      Enum.valueOf(ZOpToken.class, name);
      name = "DECORWORD";
    }
    catch (IllegalArgumentException exception) {
      try {
        // Due to the rather annoying asymmetry for the THEOREM token as a keyword/token marker
        // in both Parser and Unicode2Latex, we need to *not* consider it as Keyword, specially.
        if (!name.equals(ZKeyword.THEOREM.name()))
        {
          Enum.valueOf(ZKeyword.class, name);
          name = "DECORWORD";
          value = new Decorword(token.spelling());
        }
      }
      catch (IllegalArgumentException e) {
      }
    }
    return new Pair<String, Object>(name, value);
  }

  protected Symbol getSymbol(Token token,
                                 Map<String, Object> fieldMap)
  {
    Pair<String, Object> pair = getSymbolName(token);
    Object object = fieldMap.get(pair.getFirst());
    if (object instanceof Integer) {
      Integer result = (Integer) object;
      return new Symbol(result, pair.getSecond());
    }
    throw new CztException(token.getName() + " not found.");
  }

  @Override
  protected Class<?> getSymbolClass()
  {
    return Sym.class;
  }

  /**
   * An implementation of AbstractPrintVisitor.ZPrinter.
   */
  public static class SymbolCollector
    implements ZPrinter
  {
    private final List<Symbol> symbolList_ = new Vector<Symbol>();
    private final Map<String, Object> fieldMap_;
    private final ZmlScanner scanner_;

    public SymbolCollector(Class<?> clazz, ZmlScanner scanner)
    {
      fieldMap_ = DebugUtils.getFieldMap2(clazz);
      scanner_ = scanner;
    }

    @Override
    public void printToken(Token token)
    {
      symbolList_.add(scanner_.getSymbol(token, fieldMap_));
    }

    public List<Symbol> getSymbols()
    {
      return symbolList_;
    }
  }
}
