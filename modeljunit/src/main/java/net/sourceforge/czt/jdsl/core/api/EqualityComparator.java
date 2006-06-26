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

package net.sourceforge.czt.jdsl.core.api;



/**
 * This interface defines an equality comparison on a set of objects. It is up
 * to individual implementations to define the set over which they are
 * valid and to reject those objects which they cannot compare by
 * throwing ClassCastExceptions.
 *
 * @author Maurizio Pizzonia
 * @author Luca Vismara  
 * @version JDSL 2.1.1 
 */
public interface EqualityComparator {

  /** 
   * Allows a container (or any client) to find out whether an object is
   * a member of the ordered set over which this comparator is defined.
   * @param o Any java.lang.Object
   * @return True if and only if this comparator may compare this object.
   */
  public boolean isComparable (Object o);

  
  /** 
   * Tests the two parameter objects in the set over which the comparator is
   * defined for equality.
   * @param a First Object to compare
   * @param b Second Object to compare
   * @return True if and only if a is equal to b
   * @exception ClassCastException If either object passed in as a parameter
   * is not a member of the set over which the comparator is defined.
   */
  public boolean isEqualTo (Object a, Object b) throws ClassCastException;

}
