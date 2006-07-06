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
 * A read-only lookup structure; please refer to the documentation of
 * Dictionary for more details.
 *
 * @version JDSL 2.1.1 
 * @see Dictionary
 * @see InspectableKeyBasedContainer
 *
 * @author Mark Handy
 * @author Andrew Schwerin
 * @author Luca Vismara
 */
public interface InspectableDictionary extends InspectableKeyBasedContainer {

  /**
   * This <code>Locator</code> is returned when a method that should
   * return a locator with a given key can find no such key within
   * the data structure
   */
  public static final Locator NO_SUCH_KEY =
    new InvalidLocator("InspectableDictionary.NO_SUCH_KEY");

  /**
   * Finds an object that is mapped to a particular key. 
   *
   * @param key The key mapped to search for.
   * @return The <code>Locator</code> referring to  the key-element pair
   * that was found, or NO_SUCH_KEY if it could not be found.
   * @exception InvalidKeyException if the specified key is not a valid
   * key in this container.
   * @see #NO_SUCH_KEY
   */
  public Locator find(Object key) throws InvalidKeyException;

  /**
   * Finds all elements mapped to a particular key.  The iterator
   * returned is a snapshot -- that is, it holds all locators with the
   * specified key at the moment findAll(.) is called, regardless of
   * any modifications to the container that might occur after the
   * call to findAll(.) and before the iterator is discarded.
   *
   * @param key The key to search for.
   * @return A LocatorIterator over the set of (key, element) pairs
   * whose keys match the parameter key
   * @exception InvalidKeyException if the specified key is not valid in
   * this container
   */
  public LocatorIterator findAll(Object key) throws InvalidKeyException;

  
  // nested class(es)

  /**
   * A locator that is always invalid.  Use for all constants such as
   * NO_SUCH_KEY in a failed dictionary search.
   *
 * @author Andrew Schwerin (schwerin)
   */
  static final class InvalidLocator implements Locator {

    private String msg_;

    public InvalidLocator(String msg) {
      msg_ = msg;
    }

    public InvalidLocator() {
      msg_ = "InvalidLocator is always invalid";
    }

    public Object element() throws InvalidAccessorException {
      throw new InvalidAccessorException(msg_);
    }

    public Object key() throws InvalidAccessorException {
      throw new InvalidAccessorException(msg_);
    }

  }

}
