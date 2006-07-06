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
 * The common interface for all the mutable containers in
 * JDSL.  A container is a collection of elements, each of which is a
 * generic Object.  An element can be stored multiple times in a
 * container.  All containers organize a client's data elements, and
 * the methods defined in this interface are those that any container
 * should be able to perform on the data that it is organizing and
 * storing.
 *
 * This class is distinct from the class 
 * java.awt.Container; therefore, if
 * you are importing both packages, you must refer to it by its fully
 * qualified name.
 *
 * @version JDSL 2.1.1 
 * @author Mark Handy (mdh)
 * @author Andrew Schwerin (schwerin)
 * @author Michael T. Goodrich
 * @author Roberto Tamassia
 * @author Luca Vismara (lv)
 *
 * @see InspectableContainer
 */
public interface Container extends InspectableContainer {

  /** 
   * Creates a new, empty container of the same class as this one (and
   * therefore of the same interface as this one).  That is, if
   * newContainer() is called on a NodeSequence, the Container that is
   * returned is actually a NodeSequence.  This is a use of the
   * Factory Method design pattern.
   *
   * @return A new, empty Container of the same class as this one.
   */
  public Container newContainer ();

  
  /** 
   * Changes the element stored at an accessor.
   *
   * @param a Accessor in this container
   * @param newElement to be stored at a
   * @return old element, previously stored at a
   * @exception InvalidAccessorException if a is null or does not
   * belong to this container
   */
  public Object replaceElement (Accessor a, Object newElement)
    throws InvalidAccessorException;

}
