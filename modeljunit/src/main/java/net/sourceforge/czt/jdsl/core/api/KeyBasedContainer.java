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
 * Key-based containers are containers that store (key,element) pairs;
 * each pair is represented by a Locator.  The keys might or might not
 * be ordered.  The elements are entirely arbitrary, as far as the
 * container is concerned.  Attaching a key to every element allows
 * the container to perform key-based retrievals of elements later.
 * <p>
 * Key-based containers allow duplicate keys, elements, or pairs,
 * but there is a unique locator associated with each insertion of
 * a pair.
 * Users can implement no-duplicates semantics on top of key-based
 * containers if required.
 * 
 * @see InspectableKeyBasedContainer
 * @see Container
 * @see Locator
 *
 * @version JDSL 2.1.1 
 * @author Mark Handy
 * @author Andrew Schwerin
 * @author Luca Vismara
 **/
public interface KeyBasedContainer extends InspectableKeyBasedContainer,
					   Container {

  /**
   * Inserts a (key,element) pair into this container.
   *
   * @param key the key associated with the specified element.
   * @param element the element to insert into the container.
   *
   * @return a locator associated with the inserted pair.
   *
   * @exception InvalidKeyException if <code>key</code> cannot be used
   * by this container
   */
  public Locator insert(Object key, Object element) throws InvalidKeyException;
    


  /**
   * Removes a (key,element) pair from the container.
   *
   * @param loc a locator in the container to remove
   *
   * @exception InvalidAccessorException if the locator is not valid or
   * is not contained by this container
   */
  public void remove(Locator loc) throws InvalidAccessorException;
  

  /**
   * Replaces the key in the given (key,element) pair, adjusting the
   * container as necessary.
   *
   * @param loc the locator in the container whose key should be replaced
   * @param key the new key to associate with <code>loc</code>.
   *
   * @return The old key
   *
   * @exception InvalidAccessorException If the locator is not valid
   * or is not contained by this container
   * @exception InvalidKeyException If <code>key</code> cannot be used
   * by this container
   */
  public Object replaceKey(Locator loc, Object key) throws
  InvalidAccessorException, InvalidKeyException;


}
