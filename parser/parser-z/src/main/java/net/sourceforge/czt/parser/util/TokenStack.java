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

package net.sourceforge.czt.parser.util;

import java.util.Stack;

import net.sourceforge.czt.session.Dialect;

import java_cup.runtime.Symbol;

/**
 * A stack of tokens that is initialised with the tokens provided by a scanner.
 *
 * A scanner that returns a stream of tokens can be seen as an
 * iterator, or a stack without #push method.  This class provides a
 * stack view of a scanner that allows pushing tokens back into the
 * token stream.  When initialised with a scanner, the stack contains
 * all the tokens provided by the scanner.  They are returned via the
 * #pop method.  In addition, it is possible to push tokens back into
 * the stream.  This allows, for instance, lookahead and eases the
 * manipulation of token streams.
 *
 * @author Petra Malik
 * @author Leo Freitas
 */
public class TokenStack
{
  private final CztScanner scanner_;
  private final Stack<Symbol> stack_ = new Stack<Symbol>();

  public TokenStack(CztScanner scanner)
  {
    scanner_ = scanner;
  }
  
  public Dialect getDialect()
  {
	  return scanner_.getDialect();
  }

  public Symbol pop()
    throws Exception
  {
    if (stack_.empty()) {
      Symbol result = scanner_.next_token();
      return result;
    }
    return (Symbol) stack_.pop();
  }

  public void push(Symbol symbol)
  {
    stack_.push(symbol);
  }
}
