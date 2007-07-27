/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.rules;

import java.util.Iterator;

import net.sourceforge.czt.base.ast.Term;

/**
 * Strategies for term rewriting.
 */
public class Strategies
{
  /**
   * Performs a leftmost innermost rewriting of the given term.  The
   * redex (a sub-term that can be reduced) is searched in a
   * left-to-right, bottom-up fashion.
   *
   * This algorithm is taken from the paper Mark G.J. Van den Brand,
   * Paul Klint, and Jurgen J. Vinju: Term Rewriting with Traversal
   * Functions.
   *
   * @return the rewritten term, or the original term if no rewritings
   *         have been performed.
   * @throws NullPointerException if the given term or rewriter are
   *         <code>null</code>.
   */
  public static Term innermost(Term term, RewriteOnceVisitor rewriter)
    throws UnboundJokerException
  {
    Object[] children = term.getChildren();
    boolean aChildHasChanged = false;
    for (int i = 0; i < children.length; i++) {
      if (children[i] instanceof Term) {
        Term child = (Term) children[i];
        child = innermost(child, rewriter);
        if (child != children[i]) {
          aChildHasChanged = true;
          children[i] = child;
        }
      }
    }
    if (aChildHasChanged) {
      return reduce(term.create(children), rewriter);
    }
    return reduce(term, rewriter);
  }

  private static Term reduce(Term term, RewriteOnceVisitor rewriter)
    throws UnboundJokerException
  {
    Term result = rewriter.apply(term);
    if (result != term) {
      return innermost(result, rewriter);
    }
    return term;
  }
}
