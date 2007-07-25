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

public class Strategies
{
  public static Term innermost(Term term, RewriteOnceVisitor rewriter)
    throws UnboundJokerException
  {
    Object[] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      if (children[i] instanceof Term) {
        Term child = (Term) children[i];
        children[i] = innermost(child, rewriter);
      }
    }
    return reduce(term.create(children), rewriter);
  }

  private static Term reduce(Term term, RewriteOnceVisitor rewriter)
    throws UnboundJokerException
  {
    Term result = rewriter.apply(term);
    if (result != term) return innermost(result, rewriter);
    return term;
  }
}
