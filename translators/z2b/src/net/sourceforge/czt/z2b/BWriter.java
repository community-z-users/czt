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
package net.sourceforge.czt.z2b;

import java.io.*;
import java.lang.*;
import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

import net.sourceforge.czt.z2b.*;

/**
 * This class extends java.io.PrintWriter with some B-specific print methods.
 *
 * B is the Prolog-readable syntax used as an input format for the
 * "BZ Testing Tools" (BZ-TT) Environment.
 * Note: you must call close() when finished, to flush all output.</li>
 *
 * The main responsibilities of this class are:
 * <ol>
 *  <li> Printing all kinds of strings and B-specific objects
 *    to the output .bzp file.  Expressions and predicates are
 *    handled by delegating them to the BTermWriter class.</li>
 *
 *  <li> Translating arbitrary unicode names and Z decorations
 *    into safe B identifiers.
 *    Z decorations ("'","?","!","_3" etc.) are translated to 
 *    special substrings, and all unicode characters other than
 *    [a-zA-Z0-9_] are ignored.
 *    This ensures that the result is a valid B name, but does
 *    not give a unique result for all input names.  
 *    <p>
 *    TODO: Perhaps we should map other unicode characters into 
 *          a numeric substring like "_x46ef"? *  </li>
 *
 *  <li> Indentation levels.  Each call to nl automatically adds 
 *    indentation after the newline. </li>
 *
 *  <li> Recording the current operator precedence and inserting 
 *    parentheses whenever a weaker-binding operator is nested
 *    within a tighter-binding operator.  Note that precedences
 *    follow the usual B conventions, -10 .. +10 where 10 is
 *    very tight and -10 is very loose.  To support this, all
 *    output of an operator and its arguments must be surrounded
 *    by beginPrec(N)..endPrec(N) calls.  This class maintains a 
 *    stack of these precedences.</li>
 * </ol>
 *
 * @author Mark Utting
 */
public class BWriter extends PrintWriter

{
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.z2b");

  /** This is used to help to print expressions and predicates */
  private BTermWriter term;

  /** Minimum allowable precedence */
  public static final int LOOSEST = -10;

  /** Maximum allowable precedence */
  public static final int TIGHTEST = 10;

  /**
   * Constructor for BWriter
   *
   * @param dest where to print the B output.
   *
   */
  public BWriter(Writer dest, String source) {
    super(dest);
    precStack = new Stack();
    precStack.push(new Integer(LOOSEST));
    println("/* Translated automatically from " + source + " */");
    term = new BTermWriter(this);

  }


  //============== Methods delegated from BTermWriter =============
  /** Print a Predicate */
  
  /** Print a list of predicates, separated by '&' and newlines. */
  //@ requires preds.size() > 0;
  public void printPreds(List preds) {term.printPreds(preds);}


  /** Print a single Z predicate out in B syntax.
   *  The caller is responsible for setting the precedence of
   *  the context before calling this (@link startPrec).
   */
  public void printPred(Pred p) {term.printPred(p);}


  /** Print a Z expression out in B syntax.
   *  The caller is responsible for setting the precedence of
   *  the context before calling this (@link startPrec).
   */
  public void printExpr(Expr e) {term.printExpr(e);}

  //===================== precedence stack ========================

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
   *  beginPrec(multPrec)..endPrec(multPrec) and the 3+4 subtree should be 
   *  surrounded by beginPrec(addPrec)..endPrec(addPrec).  This will
   *  cause parentheses to be added around "3+4" in the output.
   *  
   *  @param prec  The new precedence level.
   */
  public void beginPrec(int prec) {
    int oldprec = ((Integer)precStack.peek()).intValue();
    if (prec < oldprec) {
      print("(");
      sLogger.fine("beginPrec("+prec+") oldprec="+oldprec+" '('");
    }
    precStack.push(new Integer(prec));
  }

  /** Ends an output region of a given precedence.
   *  Automatically adds a closing ')' if necessary.
   *  @param prec  Must match the current precedence level.
   */
  public void endPrec(int prec) {
    int currPrec = ((Integer)precStack.pop()).intValue();
    assert prec == currPrec
      : "beginPrec..endPrec calls are not correctly nested";
      int oldprec = ((Integer)precStack.peek()).intValue();
    if (prec < oldprec) {
      print(")");
      sLogger.fine("endPrec("+prec+") oldprec="+oldprec+" ')'");
    }
   }

  //================= general printing methods ==================

  /** the current indentation level */
  private int indent = 0;

  // the name of the current section
  protected String currSection = "";


  /** Start a new line in the B file.
   *  This automatically adds the current amount of indentation 
   *  after the newline.  External clients should use start/endSection
   *  to set this correctly, internal methods should increment or
   *  decrement 'indent'.
   */
  public void nl() {
    println();
    for (int i=0; i < indent; i++)
      print("    ");
  }



  /** Start a new section/part of the B machine.
   *  @param sectName 
   *
   *  After each startSection(S), you can call continueSection(S,...) 
   *  zero or more times (for example, to print the ELSE keyword of an
   *  IF-THEN-ELSE, then you must call endSection(S) to finish the section.
   *
   *  You can also insert a complete nested section at any time.
   *  This will use deeper indentation.
   */
  public void startSection(String sectName) {
    print(sectName);
    indent++;
    if (indent <= 1) {
	nl();
    } else {
	print(" ");
    }
  }

  /** Start the second/third/... part of the current section.
   *  @param sectName 
   *
   *  After each startSection(S), you can call continueSection(S,...) 
   *  zero or more times (for example, to print the ELSE keyword of an
   *  IF-THEN-ELSE, then you must call endSection(S) to finish the section.
   *
   *  You can also insert a complete nested section at any time.
   *  This will use deeper indentation.
   */
  public void continueSection(String sectName, String part) {
    assert sectName.equals(currSection);
    indent--;
    nl();
    print(part);
    indent++;
    if (indent <= 1)
      nl();
    else
      print(" ");
  }

  /** End the current section.
   *  @param sectName 
   */
  public void endSection(String sectName) {
    assert sectName.equals(currSection);
    indent--;
    nl();
    print("END");
  }


  /** Print one Z name into the current section.
   *  @param name 
   */
  public void printName(Name name) {
    print(bName(name));
  }

  /** Print one String name into the current section.
   *  @param name 
   */
  public void printName(String name) {
    print(bName(name));
  }

  /** Print a separator.
   *  @param sep 
   */
  public void printSeparator(String sep) {
    print(sep);
    nl();
  }

  /** Convert a Z Name into a legal B name
   */
  static public String bName(Name name) {
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
    return bName(nameString);
  }


  /** Convert a string into a legal B name
   */
  static public String bName(String name) {
    String result = "";
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
}
