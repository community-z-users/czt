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
package net.sourceforge.czt.parser.z;
import java.lang.*;
import java.util.*;
import java_cup.runtime.Symbol;
import net.sourceforge.czt.parser.z.*;

/** Looks ahead in the token stream to resolve some Z ambiguities.
 *
 *  This class 'buffers' the token stream, so that it can look
 *  ahead in the token stream if necessary, to help resolve some
 *  ambiguities in the Z grammar.
 *
 *  As described in the ISO Z standard (Section 8.4, p37), the Z
 *  grammar has several ambiguities.  For example, in {x,y,z...}, if the
 *  x,y,z is followed by ':', then it is part of a declaration (a set
 *  comprehension and declares new variables x,y,z, otherwise it
 *  is a set extension, and x,y,z must already have been declared.
 *  To resolve this, whenever we come to a NAME, 
 *  this class looks ahead over (COMMA,NAME) pairs to see if they
 *  are followed by a COLON (:) token.  If they are,
 *  it returns those names as DECLNAME tokens rather than NAME tokens.
 */
class SmartScanner implements java_cup.runtime.Scanner {
  LTZscanner dumb;
  LinkedList tokens;
  SmartScanner(LTZscanner dumbscanner) {
    dumb = dumbscanner;
    tokens = new LinkedList();
  }
  
  public Symbol next_token()
    throws java.io.IOException {
    if (tokens.size() > 0) {
      Symbol result = (Symbol) tokens.removeFirst();
      debug("popping: " + result.sym);
      return result;
    }
    else {
      Symbol s1 = dumb.next_token();
      if (s1.sym != LTZsym.WORD) {
	debug("returning immediately: " + s1.sym);
	return s1;
      }
      tokens.addLast(s1);
      boolean looking = true;   // we are still looking ahead
      debug("pushing: " + s1.sym);
      while (looking) {
	Symbol s2 = dumb.next_token();
	debug("pushing: " + s2.sym);
	tokens.addLast(s2);
	if (s2.sym != LTZsym.COMMA)
	  looking = false;
	else {
	  Symbol s3 = dumb.next_token();
	  debug("pushing: " + s3.sym);
	  tokens.addLast(s3);
	  switch (s3.sym) {
	  case LTZsym.COLON:
	    looking = false;
	    // change all WORD tokens to DECLWORD.
	    Iterator i = tokens.listIterator(0);
	    while (i.hasNext()) {
	      Symbol s = (Symbol)i.next();
	      if (s.sym == LTZsym.WORD) {
		debug("converting: " + (String)s.value +
		      " to DECLWORD");
		s.sym = LTZsym.DECLWORD;
	      }
	    }
	    break;
	    
	  case LTZsym.WORD:
	    // continue the lookahead
	    break;
	    
	  default:
	    // stop, because it is not a declaration.
	    looking = false;
	    break;
	  }
	}
      }
      Symbol result = (Symbol) tokens.removeFirst();
      debug("returning: " + result.sym);
      return result;
    }
  }
  
  protected void debug(String msg) {
    System.err.println(msg);
  }
}
