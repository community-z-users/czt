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

import net.sourceforge.czt.jdsl.core.api.Comparator;



/** 
 * Compares java.lang.Integers.  
 *
 * @author Benoit Hudson (bh)
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 */
public class IntegerComparator extends AbstractComparator
  implements Comparator {

  /** 
   * @return a negative value if x1 < x2, zero if x1 == x2, and a
   * positive value if x1 > x2
   */
  public int compare (Object x1, Object x2) throws ClassCastException {
    int a = ( (Integer)x1 ).intValue();
    int b = ( (Integer)x2 ).intValue();
    if( a<b ) return -1;
    if( a>b ) return 1;
    return 0;
  }
  
  /** 
   * @param o Object you propose to compare with this comparator
   * @return Whether o is a non-null java.lang.Integer
   */
  public boolean isComparable (Object o) {
    return ((o != null) && (o instanceof Integer));
  }

}
