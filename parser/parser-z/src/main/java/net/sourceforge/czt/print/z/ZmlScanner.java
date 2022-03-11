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

import java_cup.runtime.Symbol;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.CztScannerImpl;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.parser.util.Token;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZOpToken;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionInfo;
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
  private List<Symbol> symbols_;
  private final Iterator<Token> iter_;
  protected final Dialect dialect_;

  private Symbol pre_;
  private int pos_ = 0;
  private Symbol post_;

  /**
   * Creates a new ZML scanner.
   * @param properties
   */
  protected ZmlScanner(Dialect d, Properties properties)
  {
    super(properties);
    symbols_ =  new Vector<Symbol>();
    iter_ = null;
    dialect_ = d;
  }

  public ZmlScanner(Dialect d, Iterator<Token> iter, Properties properties)
  {
    super(properties);
    iter_ = iter;
    symbols_ = null;
    dialect_ = d;
  }

  /**
   * Creates a new ZML scanner.
   * @param term
   * @param properties
   */
  public ZmlScanner(SectionInfo si, Term term, Properties properties)
  {
    super(properties);
    PrecedenceParenAnnVisitor precVisitor =
      new PrecedenceParenAnnVisitor();
    term.accept(precVisitor);
    SymbolCollector collector = new SymbolCollector(si.getDialect(), Sym.class, this);
    ZPrintVisitor visitor = new ZPrintVisitor(si, collector, properties);
    term.accept(visitor);
    setSymbols(collector.getSymbols());
    iter_ = null;
    dialect_ = si.getDialect();
  }
  
  protected void setSymbols(List<Symbol> ls)
  {
	  symbols_ = ls;
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

  @Override
  public Dialect getDialect() {
	return dialect_;
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
    private final Dialect dialect_;

    public SymbolCollector(Dialect d, Class<?> clazz, ZmlScanner scanner)
    {
      fieldMap_ = DebugUtils.getFieldMap2(clazz);
      scanner_ = scanner;
      dialect_ = d;
    }

    @Override
    public Dialect getDialect() {
    	return dialect_;
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
