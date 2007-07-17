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

import java.lang.reflect.*;

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.zpatt.ast.JokerType;

/**
 * This is a lexer for jokers.
 */
public class JokerScanner
  implements Scanner
{
  private Scanner scanner_;
  private JokerTable table_;
  private Factory factory_;

  /**
   * Indicates whether to perform a requested lookup.
   * Lookups are only performed when parsing rule paragraphs,
   * not standard Z paragraphs.
   */
  private boolean lookup_ = false;

  public JokerScanner(Scanner scanner)
  {
    scanner_ = scanner;
    factory_ = new Factory();
  }

  public JokerTable getJokerTable()
  {
    return table_;
  }

  public void setJokerTable(JokerTable table)
  {
    table_ = table;
  }

  public Symbol next_token()
    throws Exception
  {
    Symbol result = scanner_.next_token();

    if (result.sym == Sym.RULE || result.sym == Sym.PROVISO) {
      lookup_ = true;
    }
    else if (lookup_ == true && result.sym == Sym.END) {
      lookup_ = false;
    }
    else {
      result = localLookup(result);
    }

    return result;
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
    if (symbol.sym == Sym.DECORWORD || symbol.sym == Sym.DECLWORD) {
      Decorword decorword = (Decorword) symbol.value;
      String name = decorword.getName();
      JokerType jokertype = table_.getTokenType(name);
      int type = -1;
      if (jokertype != null) {
        String jokertypeString = "joker" + jokertype.toString();
        Field[] fields = Sym.class.getFields();
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
}
