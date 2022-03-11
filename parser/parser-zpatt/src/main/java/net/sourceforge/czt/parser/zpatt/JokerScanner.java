/*
  Copyright (C) 2005 Tim Miller
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.parser.zpatt;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.Properties;

import java_cup.runtime.Symbol;
import net.sourceforge.czt.parser.util.CztScanner;
import net.sourceforge.czt.parser.util.CztScannerImpl;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.LocString;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.zpatt.ast.JokerType;

/**
 * This is a lexer for jokers.
 */
public class JokerScanner
  extends CztScannerImpl
{
  private final CztScanner scanner_;
  private JokerTable table_ = null;

  /**
   * Indicates whether to perform a requested lookup.
   * Lookups are only performed when parsing rule paragraphs,
   * not standard Z paragraphs.
   */
  private boolean lookup_ = false;

  public JokerScanner(CztScanner scanner)
  {
    super();
    if (scanner == null) throw new NullPointerException();
    scanner_ = scanner;
  }
  
  public JokerScanner(CztScanner scanner, Properties prop)
  {
	  super(prop);
	  if (scanner == null) throw new NullPointerException();
	  scanner_ = scanner;
  }

  public JokerTable getJokerTable()
  {
    return table_;
  }

  public void setJokerTable(JokerTable table)
  {
    table_ = table;
  }

  @Override
public Symbol next_token()
    throws Exception
  {
    Symbol result = scanner_.next_token();

    if (isRuleStart(result)) {
      lookup_ = true;
    }
    else if (lookup_ == true && isEnd(result)) {
      lookup_ = false;
    }
    else {
      result = localLookup(result);
    }

    return result;
  }

  protected boolean isRuleStart(Symbol symbol)
  {
    return symbol.sym == Sym.RULE || symbol.sym == Sym.PROVISO;
  }

  protected boolean isEnd(Symbol symbol)
  {
    return symbol.sym == Sym.END;
  }

  protected boolean isDecorword(Symbol symbol)
  {
    return symbol.sym == Sym.DECORWORD || symbol.sym == Sym.DECLWORD;
  }

  protected Field[] getFields()
  {
    return Sym.class.getFields();
  }

  /**
   * Lookup the value of this symbol.
   */
  protected Symbol localLookup(Symbol symbol)
    throws Exception
  {
    if (lookup_ == false || table_ == null) {
      return symbol;
    }
    Symbol result = null;
    if (isDecorword(symbol)) {
      Decorword decorword = (Decorword) symbol.value;
      String name = decorword.getName();
      JokerType jokertype = table_.getTokenType(name);
      int type = -1;
      if (jokertype != null) {
        String jokertypeString = "joker" + jokertype.toString();
        Field[] fields = getFields();
        for (int i = 0; i < fields.length; i++) {
          Field field = fields[i];
          try {
            if (Modifier.isStatic(field.getModifiers())) {
              if (jokertypeString.equalsIgnoreCase(field.getName())) {
                type = ((Integer) field.get(null)).intValue();
              }
            }
          }
          catch (IllegalAccessException e) {
            throw new CztException(e);
          }
        }
        assert type != -1;
      }
      LocString locName = new LocString(name, decorword.getLocation());
      result = (type == -1) ? symbol : new Symbol(type, 
                                                  symbol.left, 
                                                  symbol.right,
                                                  locName);
    }
    else {
      result = symbol;
    }
    return result;
  }

@Override
public Dialect getDialect() {
	// TODO Auto-generated method stub
	return scanner_.getDialect();
}

@Override
protected Class<?> getSymbolClass() {
	return Sym.class; // TODO: perhaps this needs to be per extension?
}
}
