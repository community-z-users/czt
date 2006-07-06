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
 * Defines a total ordering for a set of objects.  Its
 * methods allow for the comparison of all objects in the set over
 * which the comparator is defined.  It is up to individual
 * implementations to define the set over which they are valid and to
 * reject those objects which they cannot compare by throwing
 * ClassCastExceptions.
 * <p>
 * <b>Consistency</b><br>
 * The implementation should respect the following
 * consistency constraints:
 *
 * for each pair of objects <i>a,b</i> such that <code>isComparable(a,b)</code>
 
   <ul>
     <li>
     <code>compare(a, b) == 0</code>
       <ul>
         <b>iff</b> <code>isEqualTo(a, b) </code>
       </ul> 
     <br>	
     <li>
     <code>compare(a, b) < 0 </code>
       <ul>
         <b>iff</b> <code>isLessThan(a, b) </code> <br>
         <b>and</b> <code>!isGreaterThanOrEqualTo(a, b) </code> 
       </ul>
     <br>
     <li>
     <code>compare(a, b) > 0 </code>
       <ul>
         <b>iff</b> <code>isGreaterThan(a, b) </code> <br>
         <b>and</b> <code>!isLessThanOrEqualTo(a, b) </code> 
       </ul>
   </ul>
 *
 * @author Maurizio Pizzonia (map)
 * @author Luca Vismara (lv) 
 * @version JDSL 2.1.1 
 */
public interface Comparator extends EqualityComparator {

  /**
   * A C-style comparison function that returns a negative value if the
   * first object is less than the second, a positive value if the second
   * object is less, and 0 if the two objects are equal.
   * @param a First Object to compare
   * @param b Second Object to compare
   * @return A negative value if a is less than b, 0 if they are equal, 
   * or a positive value if a is greater than b.
   */
  public int compare (Object a, Object b) throws ClassCastException;


  /** 
   * Tests the strict order of two objects in the set over which this
   * comparator is defined.
   * @param a First Object to compare
   * @param b Second Object to compare
   * @return True if and only if a is greater than b
   * @exception ClassCastException If either object passed in as a parameter
   * is not a member of the set over which the comparator is defined.
   */
  public boolean isGreaterThan (Object a, Object b) throws ClassCastException;

    
  /** 
   * Tests the strict order of two objects in the set over which this
   * comparator is defined.
   * @param a First Object to compare
   * @param b Second Object to compare
   * @return True if and only if a is less than b
   * @exception ClassCastException If either object passed in as a parameter
   * is not a member of the set over which the comparator is defined.
   */
  public boolean isLessThan (Object a, Object b) throws ClassCastException;

    
  /** 
   * Tests non-strict order of two objects in the universe over which this
   * comparator is defined.
   * @param a First Object to compare
   * @param b Second Object to compare
   * @return True if a is greater b or if a is equal to b
   * @exception ClassCastException If either object passed in as a parameter
   * is not a member of the set over which the comparator is defined.
   */
  public boolean isGreaterThanOrEqualTo (Object a, Object b) throws
  ClassCastException;

    
  /** 
   * Tests non-strict order of two objects in the universe over which this
   * comparator is defined.
   * @param a First Object to compare
   * @param b Second Object to compare
   * @return True if a is less than b or if a is equal to b
   * @exception ClassCastException If either object passed in as a parameter
   * is not a member of the set over which the comparator is defined.
   */
  public boolean isLessThanOrEqualTo (Object a, Object b) throws
  ClassCastException;

}
