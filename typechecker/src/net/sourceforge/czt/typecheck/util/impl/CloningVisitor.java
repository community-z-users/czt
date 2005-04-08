/*
  Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck.util.impl;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;

/**
 * Recursively clones terms.
 */
public class CloningVisitor
  implements TermVisitor
{
  public CloningVisitor()
  {
  }

  public Object visitTerm(Term term)
  {
    Object [] children = term.getChildren();
    Object [] args = new Object [children.length];
    for (int i = 0; i < children.length; i++) {
      Object next = children[i];
      if (next instanceof Term && next != term) {
        Term nextTerm = (Term) next;
        args[i] = nextTerm.accept(this);
      }
      else {
        args[i] = children[i];
      }
    }
    Term result = term.create(args);
    return result;
  }
}
