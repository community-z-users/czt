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
 * Implements the JDSL HashComparator interface in terms of Java's
 * native Object methods equals(.) and hashCode().
 *
 * @author Keith Schmidt (kas)
 * @version JDSL 2.1.1 
 */
public class ObjectHashComparator 
  implements net.sourceforge.czt.jdsl.core.api.HashComparator {

  /** 
    * @param o Object you propose to compare with this comparator
    * @return Whether o is non-null
    */
  public boolean isComparable (Object o) {
    return (o != null);
  }
  
  /**
    * returns x1.equals(x2)
    *
    * @param x1 the reference object in the comparison.
    * @param x2 the object tested against the reference object.
    * @return whether x1 is equal to x2
    */
  public boolean isEqualTo (Object x1, Object x2) 
    throws ClassCastException {
      return x1.equals(x2);
  }

  /** 
    * @param o Object for which you desire a hash value
    * @return a non-negative integer hash value
    */
  public int hashValue (Object o) {
    // mask off top bit to ensure non-negativity
    return (o.hashCode() & 0x7FFFFFFF); 
  }
  
}
