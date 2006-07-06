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

import java.lang.Comparable;



/** 
 * Implementation of JDSL's Comparator interface in terms of the JDK's
 * Comparable interface.  Compares any two Comparables, regardless of
 * their actual type.
 *
 * @author Mike Boilen (mgb)
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 */
public class ComparableComparator extends AbstractComparator
  implements net.sourceforge.czt.jdsl.core.api.Comparator {

  /** 
   * Invokes the <code>compareTo</code> method of <code>x1</code> on
   * <code>x2</code>.
   *
   * @param x1 A <code>Comparable</code> to which <code>x2</code> will
   * be compared.
   * @param x2 An <code>Object</code> which will be compared to
   * <code>x1</code>
   * @exception ClassCastException if <code>x1</code> is
   * <code>null</code> or not a <code>Comparable</code>
   * @see Comparable
   */
  public int compare (Object x1, Object x2) throws ClassCastException {
    if( x1 == null )
      throw new ClassCastException (" asked to compare with null");
    
    //this will generate a ClassCastException if x1 is of the wrong
    //type.
    Comparable comparable = (Comparable)x1;
    
    //This may throw exceptions depending on the implementation of x1.
    return comparable.compareTo( x2 );
  }

  /** 
   * @param o Object you propose to compare with this comparator
   * @return Whether o is a non-null <code>Comparable</code>
   * @see Comparable
   */
  public boolean isComparable (Object o) {
    return ((o != null) && (o instanceof Comparable));
  }

}
