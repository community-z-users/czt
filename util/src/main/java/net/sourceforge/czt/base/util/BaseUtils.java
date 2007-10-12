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

import java.util.List;
import java.util.ArrayList;

import net.sourceforge.czt.base.ast.*;

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
}
