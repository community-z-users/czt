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
 *  comprehension) and declares new variables x,y,z, otherwise it
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
	Symbol result;
	if (tokens.size() > 0) {
	    result = (Symbol) tokens.removeFirst();
	    debug("popping: " + result.sym);
	}
	else {
	    result = dumb.next_token();
	    if (result.sym == LTZsym.WORD) {
		debug("starting lookahead from " + (String)result.value);
		// now we look ahead for: (COMMA WORD)* COLON
		boolean matching = true;   // we are still looking ahead
		Symbol currsym = dumb.next_token();
		debug("pushing: " + currsym.sym);
		tokens.addLast(currsym);
		while (currsym.sym == LTZsym.COMMA && matching) {
		    currsym = dumb.next_token();
		    debug("pushing: " + currsym.sym);
		    tokens.addLast(currsym);
		    if (currsym.sym == LTZsym.WORD) {
			currsym = dumb.next_token();
			debug("pushing: " + currsym.sym);
			tokens.addLast(currsym);
		    }
		    else {
			matching = false;
		    }
		}
		if (currsym.sym == LTZsym.COLON && matching) {
		    // change result and all WORDs in tokens to DECLWORD.
		    debug("converting result: " + (String)result.value + " to DECLWORD");
		    result.sym = LTZsym.DECLWORD;
		    Iterator i = tokens.listIterator(0);
		    while (i.hasNext()) {
			Symbol s = (Symbol)i.next();
			if (s.sym == LTZsym.WORD) {
			    debug("converting: " + (String)s.value + " to DECLWORD");
			    s.sym = LTZsym.DECLWORD;
			}
		    }
		}
	    }
	    debug("returning: " + result.sym);
	}
	return result;
    }

    private void debug(String msg) {
	// System.err.println(msg);
    }
}
