/**
Copyright 2003 Mark Utting
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
import java.util.List;
import java.util.Vector;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;

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
   * The class name of this class;
   * used for logging purposes.
   *
   * @return the name of this class.
   */
  private static String getClassName()
  {
    return "VisitorUtils";
  }

  /**
   * Returns the logger used for logging.
   *
   * @return the logger used for this class.
   */
  private static Logger getLogger()
  {
    return Logger.getLogger("net.sourceforge.czt.base.util."
                            + getClassName());
  }

  /**
   * <p>Visits all the Term elements contained in this list
   * using the accept-method of the Term with the provided
   * visitor as argument.</p>
   *
   * <p>Note that lists inside the given list are not visited.</p>
   *
   * @see #visitList
   * @param visitor the Visitor used for visiting the Term elements.
   * @param list the list to be visited.
   * @throws NullPointerException if <code>list</code> is <code>null</code>.
   */
  public static void visitList(Visitor visitor, List list)
  {
    Object[] arguments = {visitor, list };
    getLogger().entering(getClassName(), "visitList", arguments);
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Object object = iter.next();
      if (object instanceof Term) {
        ((Term) object).accept(visitor);
      }
    }
  }

  /**
   * <p>Visits a list by visiting all the Term elements
   * contained in this list using the accept-method
   * with the provided visitor as argument.
   * A list with the return values of the visit-calls,
   * or the original elements if it is not an instance
   * of <code>Term</code>, is returned.</p>
   *
   * <p>That is, for each <code>0 <= pos < list.size()</code>
   * we have <code>visitList(visitor, list).get(pos) ==
   * list.get(pos).accept(visitor)</code>
   * if <code>list.get(pos)</code> is an instance of
   * <code>Term</code>; <code>visitList(visitor, list).get(pos)
   * == list.get(pos)</code> otherwise.</p>
   *
   * <p>If the list to be returned contains exactly the same
   * elements in the same order as the given list, the given
   * list is returned.</p>
   *
   * <p>Note that lists inside the given list are not visited.</p>
   *
   * @param visitor the Visitor used for visiting the Term elements.
   * @param list the list to be visited.
   * @return a list containing the return values of the visit-calls.
   *         Argument <code>list</code> is returned unchanged
   *         iff each visit call returns the object it is visiting.
   * @throws NullPointerException if <code>list</code> is <code>null</code>,
   *         one of the elements of <code>list</code> is <code>null</code>,
   *         or one of the visit-calls returns <code>null</code>.
   */
  public static List getVisitList(Visitor visitor, List list)
  {
    Object[] arguments = {visitor, list };
    getLogger().entering(getClassName(), "getVisitList", arguments);
    boolean changed = false;
    List newList = new Vector(list.size());
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Object oldObject = iter.next();
      if (oldObject == null) {
        throw new NullPointerException();
      }
      if (oldObject instanceof Term) {
        Object newObject = ((Term) oldObject).accept(visitor);
        if (oldObject != newObject) {
          changed = true;
        }
        if (newObject == null) {
          throw new NullPointerException();
        }
        newList.add(newObject);
      } else {
        newList.add(oldObject);
      }
    }
    if (changed) {
      getLogger().fine("List has changed.");
      getLogger().exiting(getClassName(), "getVisitList", list);
      return newList;
    }
    getLogger().exiting(getClassName(), "getVisitList", newList);
    return list;
  }

  /**
   * <p>Visits all the terms and lists contained in this array
   * using the accept-method of term or the method #visitList
   * with the provided visitor as argument.</p>
   *
   * <p>Note that arrays inside the given array are not visited.</p>
   *
   * @param visitor the Visitor used for visiting the Term elements.
   * @param array the array to be visited.
   * @throws NullPointerException if <code>array</code> is <code>null</code>.
   */
  public static void visitArray(Visitor visitor, Object[] array)
  {
    Object[] arguments = {visitor, array };
    getLogger().entering(getClassName(), "visitArray", arguments);
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof List) {
        visitList(visitor, (List) object);
      } else if (object instanceof Term) {
        ((Term) object).accept(visitor);
      }
    }
  }

  /**
   * <p>Visits a term by visiting all its children returned via
   * the getChildren method of Term.  The returned term has the
   * return values of the correpsonding visit-calls as children.</p>
   *
   * @param visitor the Visitor used for visiting the term.
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
  public static Object visitTerm(Visitor visitor, Term term, boolean share)
  {
    Object[] arguments = {visitor, term, new Boolean(share)};
    getLogger().entering(getClassName(), "visitTerm", arguments);
    boolean changed = false;
    Object[] args = term.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        Object object = ((Term) args[i]).accept(visitor);
        if (object != args[i]) {
          args[i] = object;
          changed = true;
        }
      }
      else if (args[i] instanceof List) {
        List list = getVisitList(visitor, (List) args[i]);
        if (list != args[i]) {
          args[i] = list;
          changed = true;
        }
      }
    }
    if (!changed && share) {
      getLogger().exiting(getClassName(), "visitTerm", term);
      return term;
    }
    getLogger().fine("Term has changed.");
    Term newTerm = term.create(args);
    getLogger().exiting(getClassName(), "visitTerm", newTerm);
    return newTerm;
  }

  public static void visitTerm(Visitor visitor, Term term)
  {
    Object[] arguments = {visitor, term};
    getLogger().entering(getClassName(), "visitTerm", arguments);
    Object[] args = term.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        ((Term) args[i]).accept(visitor);
      }
      else if (args[i] instanceof List) {
        visitList(visitor, (List) args[i]);
      }
    }
  }

  /**
   * Prints a warning to stderr about any visitXXX methods
   * of the provided visitor that may not be called
   * because it does not implement the associated interface.
   *
   * @param visitor the visitor to be checked.
   */
  public static void checkVisitorRules(Visitor visitor)
  {
    Class visitorClass = visitor.getClass();
    Method[] methods = visitorClass.getDeclaredMethods();
    Class[] interfaces = visitorClass.getInterfaces();
    for (int i = 0; i < methods.length; i++) {
      String methodName = methods[i].getName();
      if (methodName.startsWith("visit")) {
        String interfaceName = methodName.substring(5) + "Visitor";
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
}
