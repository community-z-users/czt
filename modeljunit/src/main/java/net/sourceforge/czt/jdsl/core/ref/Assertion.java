/*
  Copyright (c) 1999, 2000 Brown University, Providence, RI
  
                            All Rights Reserved
  
  Permission to use, copy, modify, and distribute this software and its
  documentation for any purpose other than its incorporation into a
  commercial product is hereby granted without fee, provided that the
  above copyright notice appear in all copies and that both that
  copyright notice and this permission notice appear in supporting
  documentation, and that the name of Brown University not be used in
  advertising or publicity pertaining to distribution of the software
  without specific, written prior permission.
  
  BROWN UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO THIS
  SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR ANY PARTICULAR PURPOSE.  IN NO EVENT SHALL BROWN
  UNIVERSITY BE LIABLE FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL
  DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
  PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
  TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
  PERFORMANCE OF THIS SOFTWARE.
*/

package net.sourceforge.czt.jdsl.core.ref;



/** 
 * Helps to check invariant conditions in program and check
 * correctness of implementation.  Warning: not thread safe. Undefined
 * behavior if several threads fail on assertion checks
 * simultaneously.
 *
 * @author Benety Goh (bg@cs.brown.edu)
 * @version JDSL 2.1.1 
 * @deprecated Starting with Java 2 version 1.4 assertions are part of
 * the language, and thus this class is no longer necessary.
 */
public final class Assertion {

  /** 
   * private constructor so that we can't instantiate this class
   */
  private Assertion () {}

  /**
   * Never use this method to indicate bad user input; this method is
   * for asserting internal correctness of the implementation only.
   *
   * @param mustBeTrue expression that is assumed to be true
   * @exception AssertionException If mustBeTrue is false
   */
  public static void check (boolean mustBeTrue) throws AssertionException {
    if (!mustBeTrue)
      // use default assertion failure description
      throw new AssertionException();
  }

  /** 
   * Never use this method to indicate bad user input; this method is
   * for asserting internal correctness of the implementation only.
   *
   * @param mustBeTrue expression that is assumed to be true
   * @param message description of the problem
   * @exception AssertionException If mustBeTrue is false
   */
  public static void check (boolean mustBeTrue, String message)
    throws AssertionException {
    if (!mustBeTrue) 
      throw new AssertionException( message );
  }

}
