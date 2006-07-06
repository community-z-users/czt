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

import net.sourceforge.czt.jdsl.core.api.HashComparator;

/**
 * An implementation of a HashComparator for java.lang.Integers
 *
 * @author Keith Schmidt (kas)
 * @version JDSL 2.1.1 
 */ 
public class IntegerHashComparator implements HashComparator {

  /**
   * determines if the Comparator can use this Object
   */
  public boolean isComparable(Object toCompare) {
    // must check null as null passes instanceof test
    if (null == toCompare) 
      return false;
    return (toCompare instanceof Integer);
  }

  /**
   * tests equality on two Integers
   *
   * @throws ClassCastException
   */
  public boolean isEqualTo(Object first, Object second) 
    throws ClassCastException {
      return (((Integer)first).equals((Integer)second));
  }
     
  /**
   * defines a mapping f: Integer  -> \mathbb{Z} \cap [0, 2^{31} -1]
   *
   * @throws ClassCastException
   */
  public int hashValue(Object toHash)
    throws ClassCastException {
      // mask off the top bit to ensure a positive number.
      // java does not have unsigned base types.
      // this is faster than using Math.abs(Integer)
      return (((Integer)toHash).intValue() & 0x7FFFFFFF);
  }
}
