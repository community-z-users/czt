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
 * This interface provides a way of mapping any object in a set
 * to an integer, for purposes of implementing hash tables.   It is up
 * to individual implementations to define the set over which they are
 * valid and to reject those objects which they cannot convert by
 * throwing ClassCastExceptions.  This interface can be trivially
 * implemented with a call to Object.hashCode(), but it also allows
 * separation of the hashing criterion from the object itself,
 * when that is necessary.
 *
 * @author Luca Vismara  
 * @version JDSL 2.1.1 
 */
public interface HashComparator extends EqualityComparator {

  /** 
   * Returns the hash code value to be used for the object in this
   * comparator.
   * <p>
   * It is expected that hashValue will return a non-negative integer
   * as the hashcode of the Object, as is the custom for hashcodes.
   * However, there are no unsigned types to force this.
   *
   * @param obj an object acting as a key in a hash table
   * @return the hash code value of obj
   * @exception ClassCastException if the obj is not a member of the
   * set over which the comparator is defined.  
   */
  public int hashValue (Object obj) throws ClassCastException;

}
