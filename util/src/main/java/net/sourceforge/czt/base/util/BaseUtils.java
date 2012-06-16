/*
  Copyright (C) 2005, 2006, 2007 Mark Utting
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

package net.sourceforge.czt.base.util;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;
import net.sourceforge.czt.base.ast.Term;

/**
 * Utilities for Terms.
 */
public final class BaseUtils
{
  /**
   * Do not create instances of this class.
   */
  private BaseUtils()
  {
  }

  public static List<Term> collectAll(String className, Term term)
    throws ClassNotFoundException
  {
    return collectAll(Class.forName(className), term);
  }

  public static List<Term> collectAll(Class<?> c, Term term)
  {
    List<Term> result = new ArrayList<Term>();
    collectAll(c, term, result);
    return result;
  }

  public static void collectAll(Class<?> c, Term term, List<Term> result)
  {
    if (c.isInstance(term)) {
      result.add(term);
    }
    for (Object child : term.getChildren()) {
      if (child instanceof Term) {
        collectAll(c, (Term) child, result);
      }
    }
  }

  /**
   * Returns the maximal depth of the given term tree.
   * @param term
   * @return  
   */
  public static int depth(Term term)
  {
    int depth = 0;
    for (Object child : term.getChildren()) {
      if (child instanceof Term) {
        int d = depth((Term) child);
        if (d > depth) depth = d;
      }
    }
    return depth + 1;
  }
  
  public static long instaceCount(Class<? extends Term> term)
  {
    if (Modifier.isAbstract(term.getModifiers()))
      throw new IllegalArgumentException("Cannot count instances of abstract term " + term.getSimpleName());
    final String msg1 = "Term " + term.getSimpleName() + " doesn't have a method 'public static long instanceCount()'!";
    final String msg2= "Could not acquire permission to invoke 'instanceCount()' method of " + term.getSimpleName();
    try
    {
      Method method = term.getMethod("instanceCount", (Class<?>[]) null);
      try
      {
        Object result = method.invoke(null, (Object[]) null);
        if (!(result instanceof Long))
          throw new IllegalArgumentException(msg1);
        return (Long)result;
      }
      catch (IllegalAccessException ex)
      {
        throw new IllegalArgumentException(msg2, ex);
      }
      catch (IllegalArgumentException ex)
      {
        throw ex;
      }
      catch (InvocationTargetException ex)
      {
        throw new IllegalArgumentException(msg1, ex);
      }
    }
    catch (NoSuchMethodException ex)
    {
      throw new IllegalArgumentException(msg1, ex);
    }
    catch (SecurityException ex)
    {
      throw new IllegalArgumentException(msg2, ex);
    }
  }
}
