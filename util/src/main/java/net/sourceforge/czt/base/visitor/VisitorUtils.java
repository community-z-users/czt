/*
  Copyright (C) 2003, 2004, 2006, 2007 Mark Utting
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

package net.sourceforge.czt.base.visitor;

import java.lang.reflect.Method;
import java.util.Iterator;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.ReflectionUtils;
import net.sourceforge.czt.util.Visitor;

/**
 * Static methods for visiting
 * {@link net.sourceforge.czt.base.ast.Term Z terms}.
 *
 * @author Petra Malik
 */
public final class VisitorUtils
{
  /**
   * No instances of this class are needed.
   */
  private VisitorUtils()
  {
  }

  /**
   * <p>Visits all the terms (instances of {@link Term}) contained in
   * the array by calling the {@link Term#accept accept-method} with
   * the provided visitor as argument.  The array is changed to
   * contain the results of the visit calls.  The return value
   * indicates whether the array has changed, i.e., whether the return
   * value of one of the visit calls was different to the term to
   * which the accept method was applied.</p>
   *
   * @param visitor the visitor used for visiting the terms.
   * @param array the array (should not be <code>null</code>) to be visited,
   *              updated to contain the results of the visit calls.
   * @return whether the array has changed or not.
   */
  public static <R> boolean visitArray(Visitor<R> visitor, Object[] array)
  {
    boolean hasChanged = false;
    for (int i = 0; i < array.length; i++) {
      final Object object = array[i];
      if (object instanceof Term) {
        final Object result = ((Term) object).accept(visitor);
        if (result != object) {
          array[i] = result;
          hasChanged = true;
        }
      }
    }
    return hasChanged;
  }

  /**
   * <p>Visits a term by visiting all its children returned via its
   * {@link Term#getChildren getChildren method}.  The returned term
   * has the return values of the correpsonding visit-calls as
   * children.  Annotations are preserved.</p>
   *
   * @param visitor the Visitor used for visiting the children of the term.
   * @param term the term to be visited.
   * @param share a flag used to indicate whether a term whos children are
   *              returned unchanged by the visitor should be shared
   *              (returned without copying).
   * @return a term that has the return values of the visit-calls as children.
   *         Argument <code>term</code> is returned unchanged
   *         iff each visit call returns the object it is visiting and
   *         <code>share</code> is <code>true</code>.
   * @throws IllegalArgumentException if a new term cannot be created using
   *         the new children.
   * @throws NullPointerException if <code>term</code> is <code>null</code>.
   */
  public static <T extends Term> T visitTerm(Visitor<?> visitor,
                                             T term,
                                             boolean share)
  {
    Object[] args = term.getChildren();
    boolean changed = visitArray(visitor, args);
    if (!changed && share) {
      return term;
    }
    @SuppressWarnings("unchecked")
	T newTerm = (T) term.create(args);
    newTerm.getAnns().addAll(term.getAnns());
    args = null;
    return newTerm;
  }

  /**
   * <p>Visits a term by visiting all its children returned via
   * the getChildren method of Term.</p>
   */
  public static <R> void visitTerm(Visitor<R> visitor, Term term)
  {
    visitArray(visitor, term.getChildren());
  }

  /**
   * Prints a warning to stderr about any visitXXX methods
   * of the provided visitor that may not be called
   * because it does not implement the associated interface.
   *
   * @param visitor the visitor to be checked.
   */
  public static <R >void checkVisitorRules(Visitor<R> visitor)
  {
    Class<?> visitorClass = visitor.getClass();
    Method[] methods = visitorClass.getDeclaredMethods();
    Class<?>[] interfaces = visitorClass.getInterfaces();
    for (int i = 0; i < methods.length; i++) {
      String methodName = methods[i].getName();
      final String visitMethodStart = "visit";
      if (methodName.startsWith(visitMethodStart)) {
        String interfaceName =
          methodName.substring(visitMethodStart.length()) + "Visitor";
        boolean found = false;
        for (int j = 0; j < interfaces.length && !found; j++) {
          found = interfaces[j].getName().endsWith(interfaceName);
        }
        if (!found) {
          System.err.println("Warning: class "
                             + visitorClass.getName()
                             + " should implement interface "
                             + interfaceName + ".");
        }
      }
    }
  }

  /** Transitive visitor utils. It returns false if a problem has been found */
  public static boolean transitivelyCheckVisitorRules(Object o)
  {
    Class<?> visitorClass = o.getClass();
    Set<Method> methods = ReflectionUtils.getAllMethodsFrom(o, "visit");
    Set<Class<?>> interfaces =
      ReflectionUtils.getAllInterfacesFrom(o, "Visitor");
    boolean noProblems = true;
    int methodNameOffset = "visit".length();
    for (Method m : methods) {
      String termName = m.getName().substring(methodNameOffset);
      String intfName = termName + "Visitor";
      boolean found = false;
      Iterator<Class<?>> it = interfaces.iterator();
      while (!found && it.hasNext()) {
        found = it.next().getName().endsWith(intfName);
      }
      it = null;
      if (!found) {
        System.err.println("Warning: class "
                           + visitorClass
                           + " should implement interface "
                           + intfName + ".");
      }
      noProblems &= found;
    }
    return noProblems;
  }
}
