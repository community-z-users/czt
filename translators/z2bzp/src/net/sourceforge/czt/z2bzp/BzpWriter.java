/**
Copyright 2003 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z2bzp;

import java.io.PrintWriter;
import java.lang.*;
import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z2bzp.*;

/**
 * This class extends PrintWriter with extra methods to output BZP terms.
 *
 * BZP is the Prolog-readable syntax used as an input format for the
 * "BZ Testing Tools" (BZ-TT) Environment.
 *
 * The main responsibilities of this class are:
 * <ol>
 *  <li> Printing strings to the output .bzp file. </li>
 *
 *  <li> Translating arbitrary unicode names into safe BZP identifiers.
 *    This is currently done by adding a "b_" prefix (so the first
 *    letter is always valid for the beginning of a Prolog atom, and
 *    the remaining letters can be case-sensitive), translating
 *    Z decorations ("'","?","!","_3" etc.) to special substrings,
 *    and ignoring all other unicode characters except for [a-zA-Z0-9_].
 *    This ensures that the result is a valid Prolog atom, but does
 *    not give a unique result for all input names.  
 *    <p>
 *    TODO: Perhaps we should map other unicode characters into 
 *          a numeric substring like "_x46ef"?
 *  </li>
 *
 *  <li> Recording the current operator precedence and inserting 
 *    parentheses whenever a weaker-binding operator is nested
 *    within a tighter-binding operator.  Note that precedences
 *    follow the usual Prolog conventions, 0..1000, where 0 is
 *    very tight and 1000 is very loose.  To support this, all
 *    output of an operator and its arguments must be surrounded
 *    by beginPrec(N)..endPrec(N) calls.  This class maintains a 
 *    stack of these precedences. 
 *  </li>
 * </ol>
 *
 * @author Mark Utting
 */
public class BzpWriter
{
  private PrintWriter out = null;
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.z2bzp");


  /** The maximum allowed precedence.
   *  This must be just less than the Prolog precedence of ','/2.
   */
  public static final int MAXPREC = 999;

  /**
   * Constructor for BzpWriter
   *
   * @param dest where to print the BZP predicates.
   *
   */
  public BzpWriter(PrintWriter dest) {
    out = dest;
    precStack = new Stack();
    precStack.push(new Integer(0));
  }


  //@invar  precStack.size() > 0
  protected Stack precStack;

  /** Starts an output region of a given precedence.
   *  Automatically adds an opening '(' if prec is lower
   *  (more weakly binding) than the current precedence.
   *  Calls to beginPrec..endPrec must occur in nested pairs
   *  around each region of a given precedence.  For example,
   *  given the tree
   *  <code>
   *        (*)
   *        / \
   *      (+)  2
   *      / \
   *     3   4
   *  </code>
   *  the whole tree should be surrounded by 
   *  beginPrec(MultPrec)..endPrec() and the 3+4 subtree should be 
   *  surrounded by beginPrec(AddPrec)..endPrec().  This will
   *  cause parentheses to be added around "3+4" in the output.
   *  
   *  @param prec  The new precedence level.
   */
  public void beginPrec(int prec) {
    Integer newPrec = new Integer(prec);
    if (newPrec.compareTo((Integer)precStack.peek()) > 0)
      print("(");
    precStack.push(newPrec);
  }

  /** Ends an output region of a given precedence.
   *  Automatically adds a closing ')' if necessary.
   *  @param prec  Must match the current precedence level.
   */
  public void endPrec(int prec) {
    Integer currPrec = (Integer)precStack.pop();
    assert currPrec.compareTo(new Integer(prec)) == 0 
      : "beginPrec..endPrec calls are not correctly nested";
    if (currPrec.compareTo(precStack.peek()) > 0)
      print(")");
  }

  /** Print a string to the BZP file.
   *  @param str 
   */
  public void print(String str) {
    out.print(str);
  }



  /** Convert a Z Name into a legal BZP name (a Prolog atom).
   */
  static public String bzpName(Name name) {
    String nameString = name.getWord();
    Iterator i = name.getStroke().iterator();
    while (i.hasNext()) {
      Stroke st = (Stroke) i.next();
      if (st instanceof NextStroke)
	nameString += "'";
      else if (st instanceof InStroke)
	nameString += "?";
      else if (st instanceof OutStroke)
	nameString += "!";
      else if (st instanceof NumStroke) {
	NumStroke ns = (NumStroke) st;
	nameString += "_" + ns.getNumber().toString();
      }
      else
	  throw new RuntimeException("Unknown kind of stroke: " + st);
    }
    return bzpName(nameString);
  }

  /** Convert a string into a legal BZP name (a Prolog atom).
   */
  static public String bzpName(String name) {
    String result = "b_";
    for (int i=0; i<name.length(); i++) {
      char ch = name.charAt(i);
      // These are low-level ASCII checks, because we don't want
      // to output other unicode chars into Prolog.
      if ('a' <= ch && ch <= 'z'
	  || 'A' <= ch && ch <= 'Z'
	  || '0' <= ch && ch <= '9')
	result += ch;
      else switch (ch) {
      case '_': result += ch; break;
      case '\'': result += "__prime"; break;
      case '?': result += "__in"; break;
      case '!': result += "__out"; break;
      default: break;   // ignore unknown chars?
      }
    }
    return result;
  }


  /** This records the name of the current specification (Z section). */
  protected String currSpec = null;

  /** Output the BZP fact: specification(Name).
   *  @param name The name of the specification.
   */
  public void printSpecFact(String name) {
    currSpec = bzpName(name);
    out.println("specification(" + currSpec + ").");
  }

  /** Output a BZP operation fact: operation(Spec,Operation).
   *  @param opName The name of the variable being declared.
   */
  public void printOpFact(String opName) {
    out.println("operation(" + currSpec + ", " + opName + ").");
  }

  /** Start to output a BZP declaration: declaration(Spec,Kind,Name,Type).
   *  @param kind The kind of variable being declared.
   *  @param name The name of the variable being declared.
   */
  public void startDeclFact(String kind, String name) {
    out.print("declaration(" + currSpec + ", " + kind + ", " + name + ", ");
  }

  /** Start to output a BZP predicate: predicat(Spec,Kind,Name,Pred).
   *  @param kind The kind of variable being declared.
   *  @param name The name of the variable being declared.
   */
  public void startPredFact(String kind, String name) {
    out.print("predicat(" + currSpec + ", " + kind + ", " + name + ", ");
  }

  /** End the current BZP fact.
   */
  public void endFact() {
    out.println(").");
  }
}
