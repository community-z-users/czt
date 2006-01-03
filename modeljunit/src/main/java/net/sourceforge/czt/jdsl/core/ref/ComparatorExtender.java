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
 * Takes a <code>java.util.Comparator</code> and adapts it to the
 * <code>net.sourceforge.czt.jdsl.core.api.Comparator</code>.
 *
 * @author Mike Boilen (mgb)
 * @author Luca Vismara (lv)
 * @version JDSL 2.1.1 
 */
public class ComparatorExtender extends AbstractComparator
  implements net.sourceforge.czt.jdsl.core.api.Comparator {

  /**
   * The underlying comparator.
   */
  private java.util.Comparator iComparator;
  
  
  /**
   * Constructs a new comparator which adapts the given
   * <code>java.util.Comparator</code>.  
   */
  public ComparatorExtender( java.util.Comparator comparator )
  {
    iComparator = comparator;
  }
  
  /** 
   * Adapts the comparator method of the underlying comparator.
   *
   * @exception ClassCastException if the underlying comparator throws a
   * <code>ClassCastException</code>
   * @see java.util.Comparator#compare(Object,Object)
   */
  public int compare (Object x1, Object x2) throws ClassCastException {
    return iComparator.compare( x1, x2 );
  }
  
  /** 
   * Tests if an object is comparator by asking the comparator if
   * <code>compare(o,o)</code>
   * @see java.util.Comparator#compare(Object,Object)
   */
  public boolean isComparable (Object o) {
    try
      {
	//throws an exception if they aren't comparable
	iComparator.compare( o, o );
	return true;
      }
    catch( ClassCastException e )
      {
	return false;
      }
  }

}
