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
 * A read-only lookup structure in which an ordering of the keys is
 * maintained; please refer to the documentation of OrderedDictionary
 * for more details.
 *
 * @version JDSL 2.1.1 
 *
 * @see OrderedDictionary
 * @see InspectableDictionary
 *
 * @author Mark Handy
 * @author Luca Vismara
 * @author Andrew Schwerin
 */
public interface InspectableOrderedDictionary extends InspectableDictionary {

  /** 
   * Object returned from all four methodsof
   * InspectableOrderedDictionary to indicate that the user tried to
   * access before the first element of the dictionary or after the
   * last.  Note that dictionaries have special values returned from
   * lookup methods, rather than exceptions, when the lookup fails.
   */
  public static Locator BOUNDARY_VIOLATION = new InspectableDictionary.InvalidLocator("InspectableOrderedDictionary.BOUNDARY_VIOLATION");

  
  /**
   * Returns the Locator that is sequentially before another Locator
   * in this Container. If there is no such element then the returned
   * Locator will be invalid.
   *
   * @param locator An abstract position in this Container.
   *
   * @return A Locator which is sequentially before <code>
   * locator</code>. <B>Note:</B> Will return the invalid
   * BOUNDARY_VIOLATION Locator if no such locator exists.
   *
   * @exception InvalidAccessorException If <code>locator</code> is
   * invalid (For example: It does not actually reference an element
   * within this Container).
   */
  public Locator before(Locator locator) throws InvalidAccessorException;

  
  /**
   * Returns the Locator that is sequentially after another Locator in
   * this Container. If there is no such element then the returned
   * Locator will be invalid.
   *
   * @param locator An abstract position in this Container.
   *
   * @return A Locator which is sequentially after <code>
   * locator</code>. <B>Note:</B> Will return the invalid
   * BOUNDARY_VIOLATION Locator if no such locator exists.
   *
   * @exception InvalidAccessorException If <code>locator</code> is
   * invalid (For example: It does not actually reference an element
   * within this Container).
   */
  public Locator after(Locator locator) throws InvalidAccessorException;

  
  /**
   * Returns the locator with largest key less than or equal to the
   * search key.  There may exist more than one locator satisfying
   * this property; which one is returned is implementation dependent.
   *
   * @param key A valid key.
   *
   * @return The locator with largest key less than or equal to
   * <code>key</code>.  <B>Note:</B> If no such locator exists, the
   * returned locator will be BOUNDARY_VIOLATION.
   *
   * @exception InvalidKeyException If <code>key</code> is not of a
   * type accepted by this Container (For example: the key is not
   * comparable).
   */
  public Locator closestBefore(Object key) throws InvalidKeyException;

  
  /**
   * Returns the locator with smallest key greater than or equal to
   * the search key.  There may exist more than one locator satisfying
   * this property; which one is returned is implementation dependent.
   *
   * @param key A valid key.
   *
   * @return The locator with smallest key greater than or equal to
   * <code>key</code>.  <B>Note:</B> If no such Locator exists, the
   * returned locator will be BOUNDARY_VIOLATION.
   *
   * @exception InvalidKeyException If <code>key</code> is not of a
   * type accepted by this Container (For example: the key is not
   * comparable).
   */
  public Locator closestAfter(Object key) throws InvalidKeyException;

  
  /**
   * Returns the Locator that is sequentially before any other Locator
   * in this Container. If there is no such element then the returned
   * Locator will be invalid.
   *
   * @return A Locator which is sequentially before any other
   * locator. <B>Note:</B> Will return the invalid BOUNDARY_VIOLATION
   * Locator if no such locator exists.
   */
  public Locator first();

  
  /**
   * Returns the Locator that is sequentially after any other Locator
   * in this Container. If there is no such element then the returned
   * Locator will be invalid.
   *
   * @return A Locator which is sequentially after any other
   * locator. <B>Note:</B> Will return the invalid BOUNDARY_VIOLATION
   * Locator if no such locator exists.
   */
  public Locator last();

}
