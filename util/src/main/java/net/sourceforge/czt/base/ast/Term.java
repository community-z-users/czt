/*
  Copyright 2003, 2006, 2007 Mark Utting
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.base.ast;

import java.util.List;

import net.sourceforge.czt.util.Visitor;

/**
 * <p>A Z construct/term.</p>
 *
 * <p>This is the base interface for all Z constructs (also called term)
 * and thus for the AST for Z.  It contains methods that each Z term
 * must provide.</p>
 *
 * <p>Annotations can be used by tools to provide, for instance, type
 * information, location information, ect.  They can be used to attach
 * any type of information to a Z term.</p>
 *
 * <p>Note that annotations are NOT considered as children of a term,
 * that means they are not returned via the {@link #getChildren}-method.</p>
 *
 * @author Petra Malik
 * @see net.sourceforge.czt.base.ast
 */
public interface Term
{
  /**
   * <p>Accepts a visitor.</p>
   *
   * <p>This method provides support for the visitor design pattern.
   * Depending on the kind of visitor interfaces the given visitor
   * implements, the visited term chooses the visit-method which fits
   * best and returns the object that a call to this method returns.</p>

   * @param visitor the visitor that wants to visit this term.
   * @return the object which is returned by the
   *         visit-method call of the given visitor.
   * @see net.sourceforge.czt.base.visitor
   */
  <R> R accept(Visitor<R> visitor);

  /**
   * <p>Returns an array of all the children of this term,
   * thus providing the possibility to write generic
   * visitors that traverse a tree of Z terms without even knowing
   * the kind of term they are visiting.</p>
   * <p>The order and types of children is the same as the arguments
   * to the corresponding create method in the factory.
   *
   * @return an array of all the children of this term.
   */
  Object[] getChildren();

  /**
   * <p>Creates a new object of the implementing class
   * with the objects in <code>args</code> as its children.
   * The order and type of the children is similar
   * to the one returned by {@link #getChildren}.</p>
   *
   * <p>This method is intended to be used together with method
   * {@link #getChildren} by generic visitors.</p>
   *
   * @param args the children of the term to be created.
   * @return a new term <code>t</code> such that
   *   <code>this.getClass() == t.getClass()</code> and forall i
   *   <code>t.getChildren()[i] == args[i]</code>.
   * @see #getChildren
   */
  Term create(Object[] args);

  /**
   * <p>Returns a list of annotations.</p>
   *
   * <p>To add or remove elements, use the methods provided by
   * the List interface (that's why there is no need for a setter
   * method).</p>
   *
   * <p>
   * Avoid calling this method directly and prefer to check with <code>hasAnn()</code>
   * first. This delays creation of underlying arrays and lead to considerable memory
   * optimisation on large specs.
   * </p>
   *
   * @return a list of annotations (should never be <code>null</code>).
   */
  // TODO: perhaps this should be Ann derived classes only?
  List<Object> getAnns();

  /**
   * <p>Returns one of the <code>aClass</code> annotations of this
   * term, or <code>null</code> if the term does not contain an
   * annotation of this type.
   * @param <T>
   * @param aClass
   * @return
   */
  <T> T getAnn(Class<T> aClass);

  /**
   * Returns whether the annotation list size. This method is useful
   * to check whether to create underlying structure or not (e.g., getAnns() creates
   * objects if null initially). This delayed instantiation saves considerable memory
   * on large ASTs.
   * @return size of annotation list or <code>getAnns().size()</code>. If 0, no array is created.
   */
  int annsSize();

  /**
   * Returns true when <code>annsSize()</code> has more than zero elements.
   * @return
   */
  boolean hasAnn();

  /**
   * Checks whether the term has any annotation of the given class type
   * @param <T> type of annotation class
   * @param aClass class to check
   * @return whether there is an annotation of that kind or not
   */
  <T> boolean hasAnn(Class<T> aClass);

  /**
   * Removes a specific annotation, if present. If there are more than one
   * instance of T, the first one is removed. That is, the underlying annotations
   * as returned by getAnns() are checked in order using a.equals(annotation)
   * @param <T> type of annotation
   * @param annotation instance to remove
   * @return whether the given ann has been removed or not
   */
  <T> boolean removeAnn(T annotation);

  /**
   * Removes all annotations of the specific class.
   * @param <T> type of annotation
   * @param aClass class to check
   */
  <T> void removeAnn(Class<T> aClass);
}
