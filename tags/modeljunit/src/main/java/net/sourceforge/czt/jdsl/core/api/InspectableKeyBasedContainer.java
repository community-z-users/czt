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
 * Please refer to the documentation of <code>KeyBasedContainer</code>.
 *
 * @version JDSL 2.1.1 
 * @author Mike Boilen (mgb)
 * @author Andrew Schwerin (schwerin)
 * @author Mark Handy (mdh)
 * @author Luca Vismara (lv)
 * @see KeyBasedContainer
 */
public interface InspectableKeyBasedContainer extends InspectableContainer {

  /** 
   * Allows access to all the locators stored by this container.  No
   * order is guaranteed, although subinterfaces or implementations
   * may make a guarantee.  The iterator returned is a snapshot --
   * that is, it iterates over all locators that were in the container
   * at the moment that locators() was called, regardless of subsequent
   * modifications to the container.
   *
   * @return a LocatorIterator over all of the locators in the
   * container
   */
  public LocatorIterator locators();

  /**
   * Returns an iterator over all the keys stored in this
   * container. No order is guaranteed, although subinterfaces or
   * implementations may make a guarantee.  The iterator returned is a 
   * snapshot -- that is, it iterates over all keys that were in the container
   * at the moment that keys() was called, regardless of subsequent
   * modifications to the container.
   *
   * @return an iterator over all the keys stored in this container
   */
  public ObjectIterator keys();
  
}
