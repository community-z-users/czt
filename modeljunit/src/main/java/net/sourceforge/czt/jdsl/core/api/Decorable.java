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
 * Decorability is the ability to attach extra pieces of information
 * to an object.  Although there are no restrictions on how long a
 * decoration may remain attached to an object, the slow speed of most
 * implementations prevent them from being useful for any sort of
 * long-term storage.  Their primary use is in labelling an object
 * during the course of an algorithm so that the algorithm may return
 * later in its execution in order to access the label.
 * 
 * <p>Such temporary storage of information is useful in the form of
 * decoration because it allows an algorithm to be written for an
 * existing data structure without having to use secondary data
 * structures and without having to modify the internal representation
 * of the data structure.
 *
 * <p>This interface defines the methods that a decorable object must
 * implement: those of getting, setting, destroying and checking for
 * a decoration.
 *
 * <p>The decorations are based on the concept of attribute. The
 * attribute identifies a decoration among all possible ones in a
 * decorated object, and it has to be provided for accessing the
 * decoration itself.  Nothing prevents using the same attribute for
 * decoring more than one decorable object. For example, if we are
 * decorating all the positions of a graph we can use just one
 * attribute to retrieve the decoration on all positions.
 *
 * @version JDSL 2.1.1 
 * @author Luca Vismara (lv)
 * @author Andrew Schwerin (schwerin)
 * @author Maurizio Pizzonia (map) 
 */
public interface Decorable {

  /** 
   * Sets the value in the (attribute, value) entry associated with a
   * certain attribute in this decorable object.  Creates the
   * attribute if it does not already exist in this decorable object.
   *
   * @param attr The attribute to set (and create if necessary)
   * @param value the new value of the attribute in the decorable
   * object
   * @exception InvalidAttributeException if the attribute is invalid
   * (i.e. wrong class)
   */
  public void set (Object attr, Object value) throws InvalidAttributeException;


  /** 
   * Returns the value in the (attribute, value) entry associated with
   * a certain attribute, <code>attr</code>, in this decorable object.
   *
   * @param attr The attribute of which to attempt to get the value
   * @return The value associated with attribute
   * @exception InvalidAttributeException if <code>attr</code> is not
   * set or is otherwise invalid (i.e. wrong class)
   */
  public Object get (Object attr) throws InvalidAttributeException;
  

  /**
   * Removes the (attribute, value) entry associated with a certain
   * attribute, <code>attr</code>, from the decorable object.
   *
   * @param attr The attribute to destroy (eliminate)
   * @return the value associated with destroyed attribute
   * @exception InvalidAttributeException if the attribute is not set
   * or is otherwise invalid (i.e. wrong class)
   */
  public Object destroy (Object attr) throws InvalidAttributeException;

  
  /** 
   * Tests whether there is an (attribute, value) entry associated
   * with a certain attribute in this decorable object.
   *
   * @param attr The attribute for which to check this decorable
   * object
   * @exception InvalidAttributeException if attribute is invalid for
   * some reason
   */
  public boolean has (Object attr) throws InvalidAttributeException;

  /**
   * Returns an iterator over all the attributes attached to this
   * decorable.
   *
   * @return an <code>ObjectIterator</code> over all the attributes
   * attached to this decorable
   */
  public ObjectIterator attributes ();
  
}
