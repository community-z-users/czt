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
 * A container that accepts (key,element) pairs and allows later lookup
 * of the element associated with a particular key. The
 * interface allows users to perform lookup operations on the
 * container, but the container is not necessarily ordered. That is,
 * the user cannot rely on the ordering of the container (for example,
 * returned in the form of an Iterator), which depends on particulars
 * that he/she has to ignore (such as implementation details, history
 * of the methods calls, randomization).
 *
 * @version JDSL 2.1.1 
 *
 * @see OrderedDictionary
 *
 * @author Mark Handy
 * @author Luca Vismara
 * @author Andrew Schwerin
 */
public interface Dictionary extends InspectableDictionary, KeyBasedContainer {

  /**
   * Removes all the (key,element) pairs matching the parameter key.
   *
   * @param key the key to search for
   *
   * @return a LocatorIterator over the (key, element) pairs whose
   * keys match the parameter key
   *
   * @exception InvalidKeyException if the specified key is not a
   * valid key in this container
   */
  public LocatorIterator removeAll (Object key) throws InvalidKeyException;
  
}
