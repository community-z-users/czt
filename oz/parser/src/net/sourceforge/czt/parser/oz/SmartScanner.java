/**
Copyright 2003 Mark Utting.  marku@cs.waikato.ac.nz
This file is part of the CZT project: http://czt.sourceforge.net

The CZT project contains free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License as published
by the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along
with CZT; if not, write to the Free Software Foundation, Inc.,
59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.parser.oz;

import java.util.*;
import java_cup.runtime.Symbol;

/** Looks ahead in the token stream to resolve some Z ambiguities.
 *
 *  This class 'buffers' the token stream, so that it can look
 *  ahead in the token stream if necessary, to help resolve some
 *  ambiguities in the Z grammar.
 *
 *  As described in the ISO Z standard (Section 8.4, p37), the Z
 *  grammar has several ambiguities.  For example, in {x,y,z...}, if the
 *  x,y,z is followed by ':', then it is part of a declaration (a set
 *  comprehension) and declares new variables x,y,z, otherwise it
 *  is a set extension, and x,y,z must already have been declared.
 *  To resolve this, whenever we come to a NAME,
 *  this class looks ahead over (COMMA,NAME) pairs to see if they
 *  are followed by a COLON (:) token.  If they are,
 *  it returns those names as DECLNAME tokens rather than NAME tokens.
 */
class SmartScanner implements java_cup.runtime.Scanner
{
  private static final boolean DEBUG = false;

  private LatexScanner dumb_;
  private LinkedList tokens_;

  SmartScanner(LatexScanner dumbscanner)
  {
    dumb_ = dumbscanner;
    tokens_ = new LinkedList();
  }

  public Symbol next_token() throws java.io.IOException
  {
    Symbol result;

    if (tokens_.size() > 0) {
      result = (Symbol) tokens_.removeFirst();
      debug("popping: " + result.value);
    }
    else {
      result = dumb_.next_token();
      if (result.sym == LatexSym.NAME) {
        debug("starting lookahead from " + (String) result.value);

        // now we look ahead for: (COMMA WORD)* COLON
        boolean matching = true;   // we are still looking ahead
        Symbol currsym = dumb_.next_token();

        debug("pushing: " + currsym.value);
        tokens_.addLast(currsym);

        while (currsym.sym == LatexSym.COMMA && matching) {
          currsym = dumb_.next_token();
          debug("pushing: " + currsym.value);
          tokens_.addLast(currsym);
          if (currsym.sym == LatexSym.NAME) {
            currsym = dumb_.next_token();
            debug("pushing: " + currsym.value);
            tokens_.addLast(currsym);
          }
          else {
            matching = false;
          }
        }

        if (currsym.sym == LatexSym.COLON && matching) {
          // change result and all WORDs in tokens to DECLWORD.
          debug("converting result: " + (String) result.value + " to DECLWORD");
          result.sym = LatexSym.DECLWORD;
          Iterator i = tokens_.listIterator(0);
          while (i.hasNext()) {
            Symbol s = (Symbol) i.next();
            if (s.sym == LatexSym.NAME) {
              debug("converting: " + (String) s.value + " to DECLWORD");
              s.sym = LatexSym.DECLWORD;
            }
          }
        }
      }
      debug("returning: " + result.value);
    }
    return result;
  }

  private void debug(String msg)
  {
    if (DEBUG) {
      System.err.println(msg);
    }
  }
}
